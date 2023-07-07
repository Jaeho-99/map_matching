from rtree import index
#import pandas as pd
#from geopandas import GeoDataFrame
import heapq
#import csv
import math
from shapely.geometry import LineString, Point
import time
import numpy as np
import os
import random

def norm(diff):
    return math.sqrt((diff[0])**2 + (diff[1])**2)

class transNode:
    def __init__(self,eid = 0 ,ep = 0,pgeom = 0 ,lamb = 0,po = 0):
        #tp,prev는 가장 높은 확률을 가지는 이전 노드
        self.eid = eid
        self.pgeom = pgeom
        self.lamb = lamb
        #self.ls = ls
        #self.lr = lr
        self.ep = ep
        self.tp = 0
        self.stackp = -np.inf
        #self.prevalue = -1e+10 # value가 음수가 나오는 경우도있음.
        self.preid = -1
        self.po =  po #Point 객체
        
    def printNode(self):
        print(f"eid:{self.eid}")
        print(f"stackp:{self.stackp}")
        print(f"ep:{self.ep}")
        print(f"tp:{self.tp}")
        #print(f"prevalue:{self.prevalue}")#
       # print(f"lr:{self.lr}")
        #print(f"ls:{len(self.ls)}")
        if self.preid != -1: print(f"preid:{self.preid.eid}")
        else: print(f"preid:{self.preid}")

class transNodeList:
    def __init__(self, nodelist, std=0):
        self.nodelist = nodelist
        self.std = std
        self.tp_beta = 0
    def update_node_list(self):
        #node_list 한바퀴 돌아가면서 tp값과 베타값을 stackp에 추가.
        for node in self.nodelist:
            node.stackp -= node.tp # 복원
            node.stackp += node.tp/self.tp_beta


def make_rtree(arcs,nodes):
    # bounds 생성
    for i, (u, v) in enumerate(arcs):
        #left, bottom, right, top
        node_u = nodes[u]
        node_v = nodes[v]
        left = node_u[0]
        right = node_v[0]
        bottom = node_u[1]
        top = node_v[1]
        #g = LineString([node_u,node_v])
        if node_u[0] > node_v[0]:
            left, right = right, left
        if node_u[1] > node_v[1]:
            top, bottom = bottom , top
            
        yield (i, (left, bottom, right, top),(u,v))



#dataframe은 속도가 느림.
class Network:
    def __init__(self,arcs,nodes):
        #rtree에 edges내용물 집어넣음
        

        self.rtree = index.Index(make_rtree(arcs,nodes))
        self.arcs = arcs
        #rtree insert: yield version
        
        #coords = np.array(list(e['geometry'].coords))
        #e_bbox = e['geometry'].bounds
        #self.rtree.insert(i,e_bbox,obj=e['geometry'])
        self.edges = dict()
        self.uv_dic = dict()
        self.nodes = np.array(nodes)
        self.edges_or = []
        for i,(u,v) in enumerate(arcs):
            g = LineString([nodes[u],nodes[v]])
            #nodes 추가 필요없음.           
            #edges 추가
            self.uv_dic[(u,v)] = i 
            self.edges_or.append({'u':u,'v':v,'geometry':g})
            if u not in self.edges:
                self.edges[u] = dict()
            self.edges[u][v] = g.length
                

        #node_connect:
        
         
    def intersect(self, region):
        #rtree에 geom 겹치는 부분이 있는지 물어보는 쿼리
        #left down right up
        return self.rtree.intersection(region)

            
    def dikstra_algorithm(self,u,v,limit = 0.02):
        #u -> v까지 최단경로.
        check = set()
        que = []
        heapq.heappush(que,(0.,u))
        
        while que:
            #print(que)
            dist,cur = heapq.heappop(que)
            #print(f"cur : {cur}, dist : {dist}")
            if cur in check:
                continue
            if cur == v:
                return dist
            
            # limit 조건을 걸어두면 None이 나오는경우가 많아서 제외
            if dist > limit:
                return None
            
            check.add(cur)
            #print(cur)
            if cur in self.edges:
                nlist = list(self.edges[cur].keys())
                ndlist = list(self.edges[cur].values())
                for n,nd in zip(nlist,ndlist):
                    heapq.heappush(que,(dist + nd,n))
                
            # cur과 연결된 nodes를 추가.
            
    def dikstra_md(self,source,dests,limit = 0.02):
        #dests가 다 결정됐는지 표시.
        #dists : 결과 거리 배열
        
        result = [-1] * len(dests)
        length = len(dests)
        dests_dict = dict()
        for n,eid in enumerate(dests):
            if eid not in dests_dict:
                dests_dict[eid] = [n]
            else:
                dests_dict[eid].append(n)

        h = []
        heapq.heappush(h,(0,source))
        check = set()
        l = 0
        while h and l<length:
            dist, node =heapq.heappop(h)
            if node in check:
                continue
            #dist < limit 조건.
            if dist > limit:
                break
            if node in dests_dict:
                for dest in dests_dict[node]:
                    result[dest] = dist
                    l += 1
            check.add(node)
            if node in self.edges:
                nlist = list(self.edges[node].keys())
                ndlist = list(self.edges[node].values())
                for n,nd in zip(nlist,ndlist):
                    if n not in check:
                        heapq.heappush(h,(dist + nd,n))
        # dist 가 -1인것 다 None으로 표시
        for i in range(len(result)):
            if result[i] == -1:
                result[i] = None
        return result
    
    def singleDikstra(self,src,radius,st_dict):
        #nidx에 해당하는 노드로 다익스트라 
        #source,target, dist, next_v, next_e, prev_v
        
        cdict= {src} # 최소 거리가 결정된 node들
        que = []
        src_node = self.nodes[src]
        #초기화
        #if 조건 함수 밖에서 추가.
        for trg , dist in list(self.edges[src].items()):
            trg_node = self.nodes[trg]
            if norm(src_node - trg_node) > radius:
                continue
            heapq.heappush(que,(dist,trg))
        
        while que:
            #cur : 최단거리가 결정된 좌표.
            cur_dist, cur_trg = heapq.heappop(que) 
            if cur_trg in cdict:
                continue
            else:
                #집합 추가
                cdict.add(cur_trg)
                st_dict[(src,cur_trg)] = cur_dist
                if cur_trg not in self.edges:
                    continue
                for trg , dist in list(self.edges[cur_trg].items()):
                    #print("cdict:",cdict)

                    #Upper bound check
                    trg_node= self.nodes[trg]
                    if norm(src_node - trg_node) > radius:
                        continue
                    heapq.heappush(que,(cur_dist+dist,trg))
                    
    def dikstra_algorithm_path(self,u,v):
        #경로가없는경우 ? 생각 굳이 안해도될듯. 그런 경우가 없어보임.
        #경로 반환.
        pre_dict = dict()
        que = []
        if u == v:
            return []
        # info[0] : 도착점, info[1]: 이전노드
        heapq.heappush(que,(0.,[u,None]))
        
        while que:
            dist,info = heapq.heappop(que)
            #print(f"cur : {info}, dist : {dist}")
            if info[0] in pre_dict:
                continue
            if info[0] == v:
                # path 구하기
               # print(f"lats path")
                node_path = [info[0]]
                temp = info[1]
                while temp != u:
                    #print(temp)
                    node_path.append(temp)
                    temp = pre_dict[temp]
                node_path.append(temp) #last u node
                #print(node_path)
                node_path.reverse()
                return node_path
            
            pre_dict[info[0]] = info[1]
            if info[0] in self.edges:
                next_list = list(self.edges[info[0]].keys())
                next_dist_list = [l for l in list(self.edges[info[0]].values())]
                for n,nd in zip(next_list,next_dist_list):
                    heapq.heappush(que,(dist + nd,[n,info[0]]))
    
                
    def get_intersect(self,row,r,k):
        #k개 제한 있음
        #row : list
        # return : [(eid, dist) ]
        po = Point(row)
        all_eids=list(self.rtree.intersection((row[0] - r ,row[1]-r,row[0]+r,row[1]+r)))
        #numpy로 broadcasting가능하다면 하는게 더 빠를듯.
        all_dists=[po.distance(self.edges_or[i]['geometry']) for i in all_eids]
        #all_dists=[1/po.distance(self.edges_or[i]['geometry']) for i in all_eids]
        #all_dists_sum = sum(all_dists)
        infos=list(zip(all_eids,all_dists))
        infos.sort(key=lambda a:a[1]) #reverse?
        #print(infos)
        return [eid for eid, _ in infos[:k] ] , [dist for _,dist in infos[:k]]
    
    def searchKnn(self, traj, k,r=0.0005):
        #traj :Linestring(str)
        #left down right up
        
        #candidate node 만들기
        #traj_list =frLs(traj)
        
        cds = []
        #unmatch = []
        
        #Point(traj_list[0])
        for num,row in enumerate(traj):
            po = Point(row)
            eids,dists = self.get_intersect(row,r,k)
            #eids : 최종 k개 후보
            #eids = list(self.rtree.nearest((row[0] - r ,row[1]-r,row[0]+r,row[1]+r), k))

            cd=[]
            #len_sum = sum([self.edges_or[eid]['len'] for eid,dist in eids[:k]])

            #std = np.std(dists) # 표준편차 계산
            std = np.sum(dists)
            for eid,dist in zip(eids,dists):
                line = self.edges_or[eid]['geometry']
                lamb = line.project(po)
                pgeom = line.interpolate(lamb)
                ep = dist
                
                cd.append(transNode(eid=eid,ep=ep,pgeom=np.array(pgeom),lamb=lamb,po=po))#ep 수정해야해
            
            if cd:
                cds.append(transNodeList(nodelist = cd, std = std))
            #else:
            #    unmatch.append(num)
                
        return cds #,unmatch
    
    
#amtch_wkt 에서 어디서 시간이 많이 걸리는지 분석.
#rtree 가 문제인거아니야

#amtch_wkt 에서 어디서 시간이 많이 걸리는지 분석.
#rtree 가 문제인거아니야
class FMM:
    def __init__(self,network,cinfo = None):
        #FMM 모델만들기
        #ubodt : src,trg index 되어있는 df
        #network : Network
        ubodt  = dict()
        if cinfo is not None : 
            dist = cinfo['dist'].to_numpy()
            prev = cinfo['prev_v'].to_numpy()
            nextv = cinfo['next_v'].to_numpy()
            nexte = cinfo['next_e'].to_numpy()
            key = cinfo.index.to_numpy()
            for k,d,p,n,e in zip(key,dist,prev,nextv,nexte):
                #next_e 일단 고려 X
                ubodt[k] = {'dist':d, "prev":p,"nextv":n,"nexte":e}       
        self.ng = network
        self.ubodt = ubodt
        
    def emiss(self,dist,gps_error):
        #return -(dist)/(2*gps_error)
        return -((dist)**2)/(2*gps_error**2)
        #left,right 매칭
    def copy_trans_list(self,dest,to):
        #to는 빈 리스트.
        #dest ; 복사하력하는 transNode list
        for _ in range(len(dest)):
            to.append(transNode())
            #복사된 transNode.
            
        for dnode,tnode in zip(dest,to):
            tnode.eid = dnode.eid
            tnode.ep = dnode.ep
            tnode.pgeom = dnode.pgeom
            #초기화
            #tnode.stackp = -1e+10
            
            # stackp 반영
            tnode.stackp = dnode.stackp
    def set_trans_list(self, cdslist,mids,fmm_config):
        # trend matching에 필요한 복사본 반환.
        #cdslist[0] : out_idx
        #cdslist[-1] : cid(std)
        #out, left, std, right
        
        node_list = [[] for i in range(4)]
        self.copy_trans_list(dest= cdslist[0].nodelist ,to =node_list[0])
        self.copy_trans_list(dest = cdslist[-1].nodelist , to = node_list[2])
        for i in node_list[2]:
            #std 담당 node_list들 초기화
            i.stackp = -np.inf

        #초기화 : stackp를 이용 안할 경우.
        #for fnd in node_list[0]:
        #    fnd.stackp = 0
        
        #lmid
        self.make_mid_node(node_list, mids[0], 1 ,fmm_config)
        
        #rmid
        self.make_mid_node(node_list, mids[1], -1 ,fmm_config)
        
        return [transNodeList(cd) for cd in node_list]
    def make_mid_node(self,node_list, mid, idx, fmm_config):
        eids,dists = self.ng.get_intersect(row = mid, r = fmm_config['r'], k = fmm_config['k'])
        #print(eids)
        # mid transNode 만들기
        for _ in range(len(eids)):
            node_list[idx].append(transNode())
        #직접 값 찾아서 node list 만들어야함.
        for eid,dist,node in zip(eids,dists,node_list[idx]):
            line = self.ng.edges_or[eid]['geometry']
            lamb = line.project(Point(mid))
            node.pgeom = np.array(line.interpolate(lamb))
            node.ep = dist
            node.stackp = -np.inf
            node.eid = eid       
            
    def match_trans_list_v2(self,cds,cid,edist,gps_error,beta):
        #i -> j의 모든 tp를 한까번에 구함.
        dests =[self.ng.edges_or[j.eid]['u'] for j in cds[cid+1].nodelist]
        length = len(cds[cid+1].nodelist)
        for ni,i in enumerate(cds[cid].nodelist):
            if i.stackp == -np.inf:
                continue
            uv_sp_dists = self.ng.dikstra_md(self.ng.edges_or[i.eid]['v'],dests,limit = edist + 0.02)
            for nj, j in enumerate(cds[cid+1].nodelist):
                route_dist = uv_sp_dists[nj]
                if route_dist == None and i.eid != j.eid:
                    continue
                #ep, tp 계산.
                ijtp = self.trans_md(i,j,edist,route_dist,beta)
                jep = self.emiss(j.ep,gps_error)
                allp = ijtp + jep
                value = i.stackp + allp
                
                if value > j.stackp:
                    j.preid = i
                    j.tp = ijtp #디버깅 용
                    j.stackp = value
            
        #모두 None인경우 check
        check = -np.inf
        for node in cds[cid+1].nodelist:
            check = max(check,node.stackp)
        
        if check == -np.inf:
            for node in cds[cid+1].nodelist:
                node.stackp = 0
            return True
        return False
    def trend_match(self,cdslist,distlist,mids, fmm_config, scale_factor):
        #g(out), lmid, g(t), right
        #cdslist : cds[out], cds[std]
        #mids : [lmid, rmid]
        
        #make trend_list
        trend_list = self.set_trans_list(cdslist,mids,fmm_config)

        #g(out) lmid g(t) 까지 default match
        for cid, dist in enumerate(distlist[:2]):
            self.match_trans_list_v2(cds = trend_list,cid = cid,edist = dist,
                                     gps_error = fmm_config['gps_error'],beta = fmm_config['beta'])
        
        #g(t) rmid 계산, g(t)값에 트렌드 매칭값 추가하기.
        rmid, gt, edist = trend_list[3],trend_list[2],distlist[2]
        
        
        dests = [self.ng.edges_or[j.eid]['u'] for j in rmid.nodelist]
        #node_num = 0
        for ni, i in enumerate(gt.nodelist):
            toNode = cdslist[-1].nodelist[ni]
            if toNode.stackp == -np.inf:
                #trend하기 앞서, default match 자체가 안되는 경우.
                continue
            max_stackp = -np.inf
            uv_sp_dists = self.ng.dikstra_md(self.ng.edges_or[i.eid]['v'],dests,limit = edist + 0.02)
            for nj, j in enumerate(rmid.nodelist):
                route_dist = uv_sp_dists[nj]
                if route_dist == None:
                    #none_num += 1
                    continue
                #ep, tp 계산.
                ijtp = self.trans_md(i,j,edist,route_dist,fmm_config['beta'])
                jep = self.emiss(j.ep, fmm_config['gps_error'])
                allp = ijtp + jep
                value = allp + i.stackp
                if  max_stackp < value:
                    max_stackp = value
                    
            #trend 결과 g(t) cds에 반영
            max_stackp /= scale_factor
            if max_stackp != -np.inf:
                toNode.stackp += max_stackp
        
        #모두 None인경우 
        
    def trans_md(self,i,j,edist,route_dist,beta):
        sp_dist = None
        if i.eid == j.eid:
            sp_dist = norm(i.pgeom - j.pgeom)
        else:
            #i.pgeom , iv 
            inode, jnode = self.ng.edges_or[i.eid]['v'] , self.ng.edges_or[j.eid]['u']
            icoords, jcoords = self.ng.nodes[inode], self.ng.nodes[jnode]
            sp_dist = route_dist + norm(i.pgeom - icoords) + norm(j.pgeom - jcoords)
            
        return -abs(edist - sp_dist)/beta      
            
    def match_trans_list(self,cds,cid,edist,gps_error,beta):
        
        for nj,j in enumerate(cds[cid+1].nodelist):
            #cur node : j
            #tp를 한꺼번에 구할것.
            
            for ni,i in enumerate(cds[cid].nodelist):
                "tp"
                ijtp = self.trans(i,j,edist,beta)
                
                if ijtp is None:
                    # 최단거리가없는상황
                    continue
                # current j : cid + 1 
                
                "ep"
                #jep =  self.emiss(j.ep,cds[cid+1].std)
                jep =  self.emiss(j.ep,gps_error)
                "cal allp"
                allp = ijtp + jep 
                #allp = math.log(ijtp) + math.log(ijep)
                value = i.stackp + allp
                if value > j.stackp : 
                    j.preid= i
                    j.tp = ijtp
                    j.stackp = value
    
    
    def back_track(self,cds):
        opath = []
        result_id, temp, num =0,0,len(cds) - 1
        while num > 0 :
            opath.append([])
            LNode = max(cds[num].nodelist, key= lambda a:a.stackp)
            while LNode.preid != -1 :
                opath[result_id].append(LNode.eid)
                num -= 1
                LNode = LNode.preid
            opath[result_id].append(LNode.eid)
            num -= 1
            result_id += 1
        #맨 마지막꺼 delete : 코드 이쁘게 보이려면 필요.
        opath.reverse()
        for o in opath:
            o.reverse()
        return {
            'opath' :opath,
        },cds
        # cds는 디버깅용. 결과볼시 빼줄것.
        return {'opath':opath} , cds
    
    def default_match_wkt(self, wkt_list , fmm_config):
        
        #init node
        gps_error, beta = fmm_config['gps_error'], fmm_config['beta']
        cds = self.ng.searchKnn(wkt_list,k=fmm_config['k'],r=fmm_config['r'])
        #지도만들때를 대비
        #if unmatch:
        #    return {'unmatch':unmatch}
        for fcd in cds[0].nodelist:
            fcd.stackp = 0 
        #nodes stackp
        
        last_idx, cid = len(cds)-1 , 0 
        # 각 left, right에 빈 transNode list"""
        cid = 0
        for cid in range(last_idx):
            #print(f"-------{cid}")
            ipo = wkt_list[cid]
            jpo = wkt_list[cid+1]
            edist = norm(ipo-jpo) # np.linalg.norm 보다 일차원 배열엔 효율적
            #print(f"cid:{cid,cid+1}, edist:{edist}")
            
            #기존 알고리즘
            self.match_trans_list_v2(cds,cid,edist,gps_error,beta)
            #self.match_trans_list(cds,cid,edist,gps_error,beta)
        #backtrack
        return self.back_track(cds)
    
    def get_mid_idx(self,wkt_list,cid,w_config,last_idx,start_idx = 0):
        wstart = max(start_idx,cid - w_config + 1 )
        wend = min(last_idx ,w_config + cid - 1)
        lmid = wkt_list[wstart:cid + 1].mean(axis = 0)
        rmid = wkt_list[cid : wend + 1].mean(axis = 0)
        out_idx = max(0, wstart - 1)
        return lmid,rmid, out_idx
    
    def match_wkt(self,wkt_list,fmm_config):
        #wkt : list로 수정. 원래는 str(LineString...)
        #fmm_config : r, k, gps_error

        #init node
        gps_error, beta, w = fmm_config['gps_error'], fmm_config['beta'],fmm_config['w']
        cds = self.ng.searchKnn(wkt_list,k=fmm_config['k'],r=fmm_config['r'])
        
        #지도만들때를 대비. 없어도 되는 코드
        #if unmatch:
        #    return {'unmatch':unmatch}
        
        for fcd in cds[0].nodelist:
            fcd.stackp = 0 
        #nodes stackp
        
        cid , start_idx, last_idx = 0,0,len(cds) -1 
        #print("fm 전: ")
        
        for cid in range(last_idx):
            ipo = wkt_list[cid]
            jpo = wkt_list[cid+1]
            edist = norm(ipo-jpo) # np.linalg.norm 보다 일차원 배열엔 효율적
            #print(f"cid:{cid,cid+1}, edist:{edist}")
            
            #mid 좌표 구하기.
            lmid , rmid, out_idx = self.get_mid_idx(wkt_list,cid,w,last_idx,start_idx)
            
            #Tr_{new} 포인트끼리 거리 구하기
            dist1,dist2,dist3 = norm(lmid - wkt_list[out_idx] ),norm(lmid - wkt_list[cid]),norm(rmid - wkt_list[cid])

            self.trend_match([cds[out_idx],cds[cid]], [dist1,dist2,dist3], [lmid,rmid], fmm_config,
                            2*(out_idx - start_idx) + 3)
            
            if self.match_trans_list_v2(cds,cid,edist,gps_error,beta):
                #모두가 None이 나오는 경우
                start_idx = cid + 1
    
       # 마지막 node에 대해 trend update
        #cid == last_idx
        lmid, rmid, out_idx = self.get_mid_idx(wkt_list,last_idx,w,last_idx,start_idx)
        dist1,dist2,dist3 = norm(lmid - wkt_list[out_idx] ),norm(lmid - wkt_list[cid]),norm(rmid - wkt_list[cid])
        self.trend_match([cds[out_idx],cds[cid]], [dist1,dist2,dist3], [lmid,rmid], fmm_config,cid+1)
        
        #backtrack
        return self.back_track(cds)
    
    def spdist(self,i,j,edist):
        #i, j : transNode
        nodes = []
        ie,je = self.ng.edges_or[i.eid],self.ng.edges_or[j.eid]
        ipo,jpo = i.pgeom,j.pgeom
        #ivlist = [ie['u'],ie['v']] #geom : u->v순서
        #jvlist = [je['u'],je['v']]
        middle_dist = 0. # pgeom sp_dist
        if i.eid == j.eid:
            middle_dist = norm(ipo - jpo)
        else:
            iv,jv = ie['v'],je['u']
            #print(iv,jv)
            # pgeom ~ u / v사이 거리 계산
            inode,jnode = self.ng.nodes[iv],self.ng.nodes[jv]
            icoord,jcoord = inode,jnode
            middle_dist = norm(ipo - icoord) + norm(jpo - jcoord)
            # ubodt/dikstra 
        
            if (iv,jv) in self.ubodt:
                middle_dist += self.ubodt[(iv,jv)]['dist']
            else:
                temp = self.ng.dikstra_algorithm(iv,jv,limit = edist + 0.02)
                if temp is None:
                    return None
                middle_dist += temp
                
        return middle_dist
        
    
    def trans(self,i,j,edist,beta):
        #check redist 0
        #ver : 분수, exp
        #beta 추가
        
        middle_dist= self.spdist(i,j,edist)
                   
        #point trans : 
        """tp = 0 
        if middle_dist == 0 and edist == 0:
            tp = 1
        else:
            tp =  min(middle_dist, edist)/max(middle_dist, edist)
        if tp == 0:
            tp = 1e-10
        return tp,nodes"""

        #diff = - abs(edist - middle_dist)/beta
        if middle_dist is None:
            diff = None
        else:
            diff = -abs(edist - middle_dist)/beta
        return diff    
