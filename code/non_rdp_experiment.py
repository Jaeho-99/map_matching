import numpy as np
import heapq
from model import *
import traceback
#from rdp import rdp


def open_file(name, mode):
    # 0 : nodes,track, 1: arcs, route

    if mode == 0:
        f = lambda a: float(a)
    elif mode == 1:
        f = lambda a: int(a)

    file = open(name, "r")
    str_ = file.read()
    str_ = str_.strip().split('\n')
    file.close()

    return [list(map(f, i.split('\t'))) for i in str_]


def sampling_track(track, rate, start=0):
    # rate is 0 : 에러처리
    #     print("track",len(track))
    num = int(len(track) / rate)
    sample = [track[start + rate * i] for i in range(num)]
    if len(track) % rate > 0:
        sample.append(track[-1])
    # douglas-peucker
    #sample = rdp(sample, epsilon=0.001)
    #     print("sample",len(sample))
    return np.vstack(sample)


def calculate_len(path, net):
    # path : list
    all_len = 0
    for i in path:
        edge = net.edges_or[i]
        u, v = edge['u'], edge['v']
        all_len += net.edges[u][v]
    return all_len


def RMF(answer_list, unmatch_a, unmatch_m, net):
    all_len = calculate_len(answer_list, net)
    unmatch_a_len = calculate_len(unmatch_a, net)
    unmatch_m_len = calculate_len(unmatch_m, net)
    # print(all_len, unmatch_a_len,unmatch_m_len)
    return (unmatch_a_len + unmatch_m_len) / all_len


def get_unmatch_edge(answer_list, new_matching_path):
    match_dic = dict()
    for n, i in enumerate(new_matching_path):
        if i not in match_dic:
            match_dic[i] = [n]
        else:
            match_dic[i].append(n)

    # route mismatch fraction
    heap = []
    for answer_idx, eid in enumerate(answer_list):
        if eid in match_dic:
            # 반복해서 힙에 집어넣기.
            for match_idx in match_dic[eid]:
                heapq.heappush(heap, (match_idx, answer_idx))
        else:
            continue
    start_a = 0
    start_m = 0
    unmatch_a = []  #
    unmatch_m = []  #
    # 공통인것 꺼내기
    # match_limit은 항상 갱신됨.
    while heap:
        temp_m, temp_a = heapq.heappop(heap)
        # print(f"실행 :tm : {temp_m}, la : {start_a}, ta : {temp_a}")
        # 같은경우는?
        if temp_a < start_a:
            continue

        # unmatch_a 갱신:
        # print(f"실행 : m : {temp_m}, la : {limit_a}, ta : {temp_a}")
        for idx_m in range(start_m, temp_m):
            unmatch_m.append(idx_m)
        for idx_a in range(start_a, temp_a):
            unmatch_a.append(idx_a)

        # unmatch_m 갱신:
        # temp_a, temp_m : 딱 공통인 edge에 해당하는 인덱스
        start_a = temp_a + 1
        start_m = temp_m + 1
    # print(start_m, start_a)
    # 나머지 끝 idx 포함.
    for idx_m in range(start_m, len(new_matching_path)):
        unmatch_m.append(idx_m)
    for idx_a in range(start_a, len(answer_list)):
        unmatch_a.append(idx_a)

    return [answer_list[i] for i in unmatch_a], [new_matching_path[i] for i in unmatch_m]


# make matching route
# [3,3,3,3,4,4,5,3] => [3,4,5,3]으로바꾸기. matching_path

def preprocess(result):
    # result : [[]]
    mpath = []
    for rid in range(len(result)):
        opath, temp = result[rid], []
        temp.append(opath[0])
        for i in range(1, len(opath)):
            if opath[i] != temp[-1]:
                temp.append(opath[i])
        mpath.append(temp)
    return mpath


def shortest_matching_path(ppath, net):
    # [1,2,3,4] = > 최단거리반영한걸로변경
    # ppath : [[]], net : Network
    mpath = []
    for rid in range(len(ppath)):
        opath, temp = ppath[rid], []
        # print(matching_path)
        for i in range(len(opath) - 1):
            temp.append(opath[i])
            ueid, veid = opath[i], opath[i + 1]
            start, end = net.edges_or[ueid]['v'], net.edges_or[veid]['u']
            node_list = net.dikstra_algorithm_path(start, end)

            ##############################################
            # 왜 node들로 안하지? RMF 알고리즘 어케구현햇는지보자.
            for j in range(len(node_list) - 1):
                u, v = node_list[j], node_list[j + 1]
                temp.append(net.uv_dic[(u, v)])
        temp.append(opath[-1])
        mpath.append(temp)

    return mpath

    # single dikstra


def get_matching_path(result, net):
    ppath = preprocess(result)
    mpath = shortest_matching_path(ppath, net)
    rpath = []
    for m in mpath:
        rpath += m
    return rpath


def get_rmf(read_adr, model_adr, sampling_rate, fmm_config):
    # 모든 데이터셋 rmf 값
    # sampling_rate : list
    # return : rmf value
    # open
    # read_adr= "map-matching-dataset\\"+ number +"\\+"+number+"."
    # model_adr = "map-matching-dataset\\"+ number +"\\ + model.p
    # pickle
    logger = open("log.txt", 'a')
    logger.write(f"filename :{read_adr}")

    nodes = open_file(read_adr + 'nodes', 0)
    arcs = open_file(read_adr + "arcs", 1)
    coords = open_file(read_adr + 'track', 0)
    tracks = np.array(coords)[:, :2]
    answer = open_file(read_adr + 'route', 1)
    answer_list = np.array(answer).reshape(-1).tolist()

    net = Network(arcs, nodes)
    model = FMM(network=net)

    # generate data
    sample_tracks = [sampling_track(tracks, i) for i in sampling_rate]
    sample_rmf_my = [0] * len(sample_tracks)
    sample_rmf_org = [0] * len(sample_tracks)

    for n, sample_track in enumerate(sample_tracks):
        logger.write(f"sapling_rate : {sampling_rate[n]}")
        print(sampling_rate[n])
        try:
            result_my, _ = model.match_wkt(wkt_list=sample_track, fmm_config=fmm_config)
            result_org, _ = model.default_match_wkt(wkt_list=sample_track, fmm_config=fmm_config)

            rpath_my = get_matching_path(result_my['opath'], model.ng)
            rpath_org = get_matching_path(result_org['opath'], model.ng)
            # get rmf :
            false_negative, false_positive = get_unmatch_edge(answer_list, rpath_my)
            sample_rmf_my[n] = RMF(answer_list, false_negative, false_positive, net)

            false_negative, false_positive = get_unmatch_edge(answer_list, rpath_org)
            sample_rmf_org[n] = RMF(answer_list, false_negative, false_positive, net)
        except Exception:
            logger.write(traceback.format_exc())

    logger.close()
    return sample_rmf_org, sample_rmf_my