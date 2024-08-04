"""Solve various problems concerning the formula
"""
from __future__ import absolute_import
import copy

try:
    from networkx import DiGraph
except ImportError:
    from .minnx import DiGraph

from .tstruct import stategen


def forallexists_pre(tsys, A):
    tmp = set()
    for s in A:
        # 遍历s的所有prev
        for pre_s in tsys.G.predecessors(s):
            # 遍历env 的transition
            for envpost in tsys.envtrans[pre_s]:
                canreach = False
                for post_pre_s in tsys.G.successors(pre_s):
                    if tuple([post_pre_s[i] for i in tsys.ind_uncontrolled]) != envpost:
                        continue
                    if post_pre_s in A:
                        canreach = True
                        break
                if not canreach:
                    break
            if canreach:
                tmp.add(pre_s)
    return tmp


# public BDD calculate_win() {
#       BDD Z = TRUE;
#       for (Fix fZ = new Fix(); fZ.advance(Z);) {
#            mem.clear();
#            for (int j = 1; j <= sys.numJ(); j++) {
#                BDD Y = FALSE;
#                for (Fix fY = new Fix(); fY.advance(Y);) {
#                    BDD start = sys.Ji(j).and(cox(Z)).or(cox(Y));
#                    Y = FALSE;
#                     for (int i = 1; i <= env.numJ(); i++) {
#                        BDD X = Z;
#                        for (Fix fX = new Fix(); fX.advance(X);)
#                            X = start.or(env.Ji(i).not().and(cox(X)));
#                        mem.addX(j, i, X); // store values of X
#                        Y = Y.or(X);
#                    }
#                    mem.addY(j, Y); // store values of Y
#                }
#                Z = Y;
#            }
#       }
#       return Z;
#  }
# 获取 winning 集合，表示可以合成出controller
def get_winning_set(tsys, return_intermediates=False):
    # S 和 Z都是符号化表示 (1, 1, 0, 0, 0, 1) ...
    S = set(tsys.G.nodes())
    # print("initial S" + str(S))
    # print("S len:" + str(len(S)))

    # S的 num_sgoals 个拷贝，在arbiter3里面是3
    # Z从全集，计算最大不动点，逐步收缩
    Z = [S.copy() for i in range(tsys.num_sgoals)]

    # print("initial Z" + str(Z))
    # print("Z len:" + str(len(Z)))
    change_among_Z = True
    while change_among_Z:
        change_among_Z = False
        # 拷贝当前Z作为prev Z
        Z_prev = [this_Z.copy() for this_Z in Z]
        if return_intermediates:
            Y_list = [[] for i in range(len(Z))]
            X_list = [[] for i in range(len(Z))]
        # 遍历 Z 中集合
        for i in range(len(Z)):
            # 获取 Z[i]的拷贝作为当前index的prev Z
            this_Z_prev = Z[i].copy()
            Y = set()
            if return_intermediates:
                num_sublevels = 0
            # 从Z_prev[i+1]中获取goal_progress
            goal_progress = forallexists_pre(tsys, Z_prev[(i+1) % tsys.num_sgoals])

            # goal_progress 再与满足当前系统目标 SYSGOAL[i] 的状态集合取交集。
            goal_progress &= set([s for s in S if 'SYSGOAL'+str(i) in tsys.G.nodes[s]['sat']])
            # print("after s & goal_progress:" + str(goal_progress))

            while True:
                # 计算最小不动点集合Y
                Y_prev = Y.copy()
                if return_intermediates:
                    Y_list[i].append(Y_prev)
                    num_sublevels += 1
                Y = set()
                Y_exmodal = forallexists_pre(tsys, Y_prev)
                # reach_goal_progress是 goal_progress and Y_exmodal的并集
                reach_goal_progress = goal_progress.union(Y_exmodal)
                if return_intermediates:
                    X_list[i].append([])
                for j in range(tsys.num_egoals):
                    # X是状态集合的copy，最大不动点
                    X = S.copy()
                    while True:
                        X_prev = X.copy()
                        # X 的前集通过 forallexists_pre 计算
                        X = forallexists_pre(tsys, X_prev)
                        # 去掉不满足环境目标 ENVGOAL[j] 的状态。
                        X &= set([s for s in S if 'ENVGOAL'+str(j) not in tsys.G.nodes[s]['sat']])
                        # 将 X 和 reach_goal_progress 取并集。
                        X |= reach_goal_progress
                        # 当X不再变化时退出
                        if X == X_prev:
                            break
                        X &= X_prev
                    if return_intermediates:
                        X_list[i][num_sublevels-1].append(X)
                    Y |= X
                # 当Y不再发生变化的时候，退出循环
                if Y == Y_prev:
                    if return_intermediates:
                        num_sublevels -= 1
                        X_list[i].pop()
                    break
                Y |= Y_prev
            Z[i] = Y
            # 当Z集合不再变化时退出循环迭代
            if Z[i] != this_Z_prev:
                change_among_Z = True
                Z[i] &= this_Z_prev
    if return_intermediates:
        return Z[0], Y_list, X_list
    else:
        return Z[0]

def get_initial_states(W, tsys, exprtab, init_flags='ALL_ENV_EXIST_SYS_INIT'):
    """
    If initial conditions are not satisfied on the winning set, return None.
    """
    assert init_flags.upper() == 'ALL_ENV_EXIST_SYS_INIT', 'Only the initial condition interpretation ALL_ENV_EXIST_SYS_INIT is supported.'

    evalglobals = {'__builtins__': None, 'True': True, 'False': False}
    identifiers = [v['name'] for v in tsys.symtab]

    initial_states = list()

    for state in stategen([v for v in tsys.symtab if v['uncontrolled']]):
        stated = dict(zip(identifiers, state))
        if not eval(exprtab['ENVINIT'], evalglobals, stated):
            continue
        found_match = False
        for s in W:
            if (tuple([s[i] for i in tsys.ind_uncontrolled]) == state
                and 'SYSINIT' in tsys.G.nodes[s]['sat']):
                initial_states.append(copy.deepcopy(s))
                found_match = True
                break
        if not found_match:
            return None

    return initial_states

def check_realizable(tsys, exprtab, init_flags='ALL_ENV_EXIST_SYS_INIT'):
    """
    检查realizable
    """

    W = get_winning_set(tsys)
    # If initial conditions are not satisfied on the winning set, return None.
    if get_initial_states(W, tsys, exprtab, init_flags) is None:
        return False
    else:
        return True

def synthesize(tsys, exprtab, init_flags='ALL_ENV_EXIST_SYS_INIT'):
    """
    合成controller
    """

    assert init_flags.upper() == 'ALL_ENV_EXIST_SYS_INIT', 'Only the initial condition interpretation ALL_ENV_EXIST_SYS_INIT is supported.'

    W, Y_list, X_list = get_winning_set(tsys, return_intermediates=True)
    print("W" + str(W))
    initial_states = get_initial_states(W, tsys, exprtab, init_flags)
    if initial_states is None:
        return None
    print("initial_states:" + str(initial_states))
    # goalnames 是系统目标的名称列表
    goalnames = ['SYSGOAL'+str(i) for i in range(tsys.num_sgoals)]

    #初始化Y_list ：把在W中的状态 存在SYSGOAL[i]的添加进去
    for goalmode in range(tsys.num_sgoals):
        Y_list[goalmode][0] = set([s for s in W if goalnames[goalmode] in tsys.G.nodes[s]['sat']])
    
    # 获取strategy
    strategy = DiGraph()
    next_id = len(initial_states)
    # workset 包含所有初始状态的索引。
    workset = list(range(next_id))
    # 将初始状态添加到策略图中，并标记为初始状态。
    # 这个mode是什么东西？
    """
    mode 用于跟踪系统当前所处的目标模式。在合成控制器的过程中，系统需要在不同的目标模式之间切换，以确保最终实现所有目标。具体来说：
    系统目标模式：每个 mode 对应于一个特定的系统目标（如 SYSGOAL0, SYSGOAL1, …）。
    模式切换：当系统在当前模式下达到目标时，它会切换到下一个模式，继续尝试满足下一个目标。
    状态跟踪：在构建策略图时，每个节点不仅需要记录其状态，还需要记录其模式，以确保在不同模式下采取不同的策略。
    """
    strategy.add_nodes_from([(i, {'state': s, 'mode': 0, 'initial': True})
                             for (i,s) in enumerate(initial_states)])
    # 弹出所有workset，运算结束
    while len(workset) > 0:
        """
        从 workset 中取出一个节点 nd。
        找到当前模式下 Y_list 中包含 nd 状态的集合索引 j。
        如果 j == 0，表示当前状态满足目标，更新模式并检查是否循环。
        如果找到重复节点，移除当前节点并连接到重复节点，继续下一个节点。
        """
        nd = workset.pop()

        j = 0
        while j < len(Y_list[strategy.nodes[nd]['mode']]):
            if strategy.nodes[nd]['state'] in Y_list[strategy.nodes[nd]['mode']][j]:
                break
            j += 1
        if j == 0:
            assert goalnames[strategy.nodes[nd]['mode']] in tsys.G.nodes[strategy.nodes[nd]['state']]['sat']
            original_mode = strategy.nodes[nd]['mode']
            while goalnames[strategy.nodes[nd]['mode']] in tsys.G.nodes[strategy.nodes[nd]['state']]['sat']:
                # 切换mode
                strategy.nodes[nd]['mode'] = (strategy.nodes[nd]['mode'] + 1) % tsys.num_sgoals
                if strategy.nodes[nd]['mode'] == original_mode:
                    break
            if strategy.nodes[nd]['mode'] != original_mode:
                repeat_found = False
                # 找可能的重复节点
                for possible_repeat, attr in list(strategy.nodes(data=True)):
                    if (possible_repeat != nd
                        and attr['mode'] == strategy.nodes[nd]['mode']
                        and attr['state'] == strategy.nodes[nd]['state']):
                        repeat_found = True
                        for (u,v) in strategy.in_edges(nd):
                            strategy.add_edge(u, possible_repeat)
                        strategy.remove_edges_from(
                            list(strategy.in_edges(nd)))
                        strategy.remove_node(nd)
                        break
                if repeat_found:
                    continue

            j = 0
            while j < len(Y_list[strategy.nodes[nd]['mode']]):
                if strategy.nodes[nd]['state'] in Y_list[strategy.nodes[nd]['mode']][j]:
                    break
                j += 1
            if j == 0:
                assert goalnames[strategy.nodes[nd]['mode']] in tsys.G.nodes[strategy.nodes[nd]['state']]['sat']

        """
        遍历环境后继状态 envpost。
        找到满足条件的后继状态 next_state。
        如果没有找到后继状态，寻找阻塞状态集合中的状态作为后继状态。
        如果找到匹配的节点，添加边到策略图。
        如果没有找到匹配的节点，创建一个新节点并添加到策略图和 workset 中。
        """
        for envpost in tsys.envtrans[strategy.nodes[nd]['state']]:
            next_state = None
            for succ_nd in tsys.G.successors(strategy.nodes[nd]['state']):
                if (tuple([succ_nd[i] for i in tsys.ind_uncontrolled]) == envpost
                    and ((j > 0 and succ_nd in Y_list[strategy.nodes[nd]['mode']][j-1])
                         or (j == 0 and succ_nd in W))):
                    next_state = succ_nd
                    break

            if next_state is None:
                assert j > 0
                if j == 0:
                    import pdb; pdb.set_trace()
                blocking_index = None
                blocking_sets = X_list[strategy.nodes[nd]['mode']][j-1]
                for k in range(len(blocking_sets)):
                    if strategy.nodes[nd]['state'] in blocking_sets[k]:
                        blocking_index = k
                        break
                assert blocking_index is not None
                for succ_nd in tsys.G.successors(strategy.nodes[nd]['state']):
                    if (tuple([succ_nd[i] for i in tsys.ind_uncontrolled]) == envpost
                        and succ_nd in blocking_sets[blocking_index]):
                        next_state = succ_nd
                        break
                assert next_state is not None
            
            # 状态和模式匹配
            foundmatch = False
            for candidate, cattr in strategy.nodes(data=True):
                if cattr['state'] == next_state and cattr['mode'] == strategy.nodes[nd]['mode']:
                    strategy.add_edge(nd, candidate)
                    foundmatch = True
                    break
            if not foundmatch:
                if j == 0:
                    new_mode = (strategy.nodes[nd]['mode'] + 1) % tsys.num_sgoals
                else:
                    new_mode = strategy.nodes[nd]['mode']
                # 添加新的node，设置新的mode,加入workset
                workset.append(next_id)
                strategy.add_node(
                    next_id,
                    state=next_state,
                    mode=new_mode,
                    initial=False)
                strategy.add_edge(nd, next_id)
                next_id += 1

    return strategy
