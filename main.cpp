#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <iostream>
#include <assert.h>
//#include <windef.h>

#define MAX 10010
#define MAXK 200
#define HASHNUM 131073
#define HASHNUM2 10000000
#define INF -99999999
#define BASENUM 100
#define MAXPOINT 100
#define BASETIME 5
#define MIN(x,y) (((x)<(y))?(x):(y))
using namespace std;

int Tabucircle;
int restarttime[]={1,1,2,1,1,2,4,1,1,2,4,8,1,1,2,4,8,16,1,1,2,4,8,16,32,1,1,2,4,8,16,32,64};
const int MAXCIRCLE = 100000;
int MAXTIME = 1000;
float param_alpha = 0.1f;
float param_beta = 0.4f;
int perturbflag=0;
int N,M,K,best_cost,best_temp,new_cost,improved,lastfrom,lastc1,lastc2,lastto,improvenum,circle,bestcircle;//N表示点总数，K表示团总数
int weight[MAX][MAX],sumweight[MAX];
int randlst[MAX];
int hashcluster[MAXK],clustertabu[HASHNUM2],newtabu[HASHNUM],pointmovenum[MAX],index[MAXK],backindex[MAXK],bestindex[MAXK];
int T1,T2,finalmovenum;
int ans[MAXK][MAX],p[MAX][MAXK],tabu[MAX][MAXK],tabuO[MAX][MAXK],Tabu2[MAX];//ans[i][0]中存该团内点个数
int bestK,bestans[MAXK][MAX];
int address[MAX],bestaddress[MAX];//表示每个点所在团
char param_filename[1000];
int hashZ[MAX];
int s1,s2,s3,s0,timetemp,best_time;
//int countnum=0;

int perturbnum[MAX];

typedef struct pnt_heap{
    int p_weight;
    int pnt_add;
};
pnt_heap *heap[MAX][MAX];//heap[i][0]中存i点所在团编号以及所有团数。

typedef struct pnt_move{
    int pointnum;
    double moved;
};
pnt_move movepoint[MAX];

typedef struct pnt_move2{
    int pointnum;
    int moved;
};
pnt_move2 movepoint2[MAX];

int cmp(const void*p1,const void*p2)
{
    return(*(pnt_move *)p2).moved>(*(pnt_move *)p1).moved?1:-1;
}

int comp(const void*a,const void*b)
{
    return (*(pnt_move2 *)a).moved - (*(pnt_move2 *)b).moved;
}

void pre_com_hash()
{
    int i;
    for(i=0;i<N;i++)
        hashZ[i]=rand()%100000;
}


void showUsage(){
	//TODO:
	cout << "Wrong parameter" << endl;
}

void generateRandList(int len)
{
    int idx = 0;

	for (idx = 0; idx < len; idx++)
		randlst[idx] = idx;
	for (idx = 0; idx < len; idx++)
	{
		int randid = rand() % (len-idx)+idx;
		int tmp = randlst[idx];
		randlst[idx] = randlst[randid];
		randlst[randid] = tmp;
	}
//	for (idx = 0; idx < len; idx++)
//	printf("%d ",randlist[idx]);
//	printf("\n");
}

void ReadFile(char *s)
{
    FILE *fp=fopen(s,"r");
    if(fp==NULL)
    {
        printf("ReadFile failed\n");
        exit(-1);
    }
    fscanf(fp,"%d",&N);
    printf("%d\n",N);
    for(int i=0;i<N;i++)
    {
        weight[i][i]=0;
        for(int j=i;j<N;j++){
            fscanf(fp,"%d",&weight[i][j]);
            weight[i][j]=-weight[i][j];
            weight[j][i]=weight[i][j];
        }
    }
//    for(int i=0;i<N;i++){
//    for(int j=0;j<N;j++)
//    {
//        printf("%d ",weight[i][j]);
//    }
//    printf("\n");
//    }
}

void rewritebest()
{
    int i,j;
    bestK=K;
    for(i=0;i<MAXK;i++)
        for(j=0;j<=ans[i][0];j++)
            bestans[i][j]=ans[i][j];
    for(i=0;i<MAXK;i++) {
        bestindex[i]=index[i];
    }
    for(i=0;i<N;i++)
        bestaddress[i]=address[i];
//    for(i=0;i<HASHNUM;i++)
//        newtabu[i]=0;
    return ;
}

//*
int IsTabu(int point,int p_add)
{
    int i,temp=0,num=0,temp_add=address[point],tempi;
    temp=hashcluster[p_add];
    if(temp==tabu[point][p_add]) return 1;
//    if(temp==tabuO[point][p_add]) return 1;
    temp=(temp+hashZ[point])%HASHNUM;
    for(i=1;i<=ans[p_add][0];i++)
    {
        tempi=temp-hashZ[ans[p_add][i]];
        if(tempi<0) tempi+=HASHNUM;
        if(tempi==tabu[ans[p_add][i]][p_add]) {
//            printf(" *%d %d %d",ans[p_add][i],i,p_add);
            return 1;
        }
//        if(tempi==tabuO[ans[p_add][i]][p_add]) {
////            printf(" *%d %d %d",ans[p_add][i],i,p_add);
//            return 1;
//        }
    }
    temp=hashcluster[temp_add];
    if(temp==tabu[point][temp_add]) return 1;
//    if(temp==tabuO[point][temp_add]) return 1;
//    if(address[point]==lastfrom||address[point]==lastto) num++;
//    if(p_add==lastfrom||p_add==lastto) num++;
//    if(num==2) return 1;
    return 0;
}
/*/
//同样的团不能出现
int IsTabu(int point,int p_add,int now_cost)
{
    return newtabu[(hashcluster[p_add]+hashZ[point])%HASHNUM]+newtabu[(hashcluster[address[point]]-hashZ[point]+HASHNUM)%HASHNUM];
//    if(clustertabu[now_cost]==0)
//        return 0;
//    else return newtabu[(hashcluster[p_add]+hashZ[point])%HASHNUM];
}
//*/

void p_insert(int point,int p_val,int p_add)
{
    int i,j;
    i=++heap[point][0]->p_weight;
//        assert(i==heap[point][0]->p_weight);
    j=i>>1;
    while(i>1&&p_val>heap[point][j]->p_weight)
    {
        heap[point][i]=heap[point][j];
        i=j;
        j>>=1;
    }
    heap[point][i]=(pnt_heap *)malloc(sizeof(pnt_heap));
    heap[point][i]->p_weight=p_val;
    heap[point][i]->pnt_add=p_add;
    return ;
}

void p_delete(int point,int p_add)
{
    int i,j,len=heap[point][0]->p_weight;
//    if(p[point][p_add]!=0)
//    printf("...%d %d %d\n",point,p_add,p[point][p_add]);
//    assert(p[point][p_add]==0);
    for(i=1;i<=len;i++)
        if(heap[point][i]->pnt_add==p_add)
            break;
    free(heap[point][i]);
    while(1){
        if(i<<1>=len)
        {
            if(i<len) heap[point][i]=heap[point][len];
            heap[point][0]->p_weight--;
            return ;
        }
        j=i<<1;
        j=(heap[point][j]->p_weight>heap[point][j+1]->p_weight)?j:j+1;
        heap[point][i]=heap[point][j];
        i=j;
    }
    return ;
}


void p_change(int point,int p_val,int p_add)
{
    int i,j,temp=0,len=heap[point][0]->p_weight,maxj,rightj;
    pnt_heap *h_temp;
    for(i=1;i<=len;i++)
        if(heap[point][i]->pnt_add==p_add)
            break;
    h_temp=heap[point][i];
    h_temp->p_weight=p_val;
//    assert(heap[point][i]->p_weight==p_val);
    j=i>>1;
    while(i>1&&p_val>heap[point][j]->p_weight)
    {
        temp=1;
        heap[point][i]=heap[point][j];
        i=j;
        j>>=1;
    }
    if(temp)
    {
        heap[point][i]=h_temp;
        return ;
    }
    while(1)
    {
        j=i<<1;rightj=i<<1+1;
        maxj=i;
        if(j<=len&&heap[point][i]->p_weight<heap[point][j]->p_weight)
            maxj=j;
        if(rightj<=len&&heap[point][i]->p_weight<heap[point][rightj]->p_weight)
            maxj=rightj;
        if(maxj != i)
        {
            heap[point][i]=heap[point][maxj];
            heap[point][maxj]=h_temp;
            i=maxj;
        }
        else return ;
    }
}

void InitialSolution2()//初始化五十个团
{
    int i,j,temp1,temp;
	s1=time((time_t*)NULL);
    printf("Initial\n");
    for(i=0;i<N;i++){
        ans[i][0]=0;
        for(j=0;j<N;j++)
        {
            p[i][j]=0;
        }
    }
    K=(50>N)?N:50;
    for(i=0;i<N;i++)
    {
        if(i<K)
        {
            ans[i][++ans[i][0]]=i;
            address[i]=i;
        }
        else{
            temp=rand()%50;
            ans[temp][++ans[temp][0]]=i;
            address[i]=temp;
        }
    }
    pre_com_hash();
    for(i=0;i<N;i++)
        for(j=0;j<MAXK;j++){
            tabu[i][j]=0;
            tabuO[i][j]=0;
        }
    for(i=0;i<MAXK;i++){
        index[i]=i;
        backindex[i]=i;
    }
    for(i=0;i<=N;i++)
        for(j=0;j<K;j++)
        {
            p[i][j]=0;
            for(temp1=1;temp1<=ans[j][0];temp1++)
            {
                p[i][j]+=weight[i][ans[j][temp1]];
            }
        }
    for(i=0;i<N;i++)
    {
        free(heap[i][0]);
        heap[i][0]=(pnt_heap *)malloc(sizeof(pnt_heap));
        heap[i][0]->p_weight=0;
        heap[i][0]->pnt_add=address[i];
        for(j=0;j<K;j++)
        {
            p_insert(i,p[i][j],j);
        }
    }
    new_cost=0;
    for(i=0;i<K;i++)
    {
        for(j=1;j<ans[i][0];j++)
        {
            for(temp1=j+1;temp1<=ans[i][0];temp1++)
            {
                new_cost+=weight[ans[i][j]][ans[i][temp1]];
            }
        }
    }
    if(new_cost>best_cost){
        best_cost=new_cost;
        bestcircle=circle;
        rewritebest();
    }
    printf("%d %d\n",new_cost,best_cost);
}

int findBestMove(int &tempt)
{
    int bestinc=INF,point,temp,tempinc,desw,desadd,count=0;
    int i,j;
//    int *randlst = new int[N];
    generateRandList(N);
    for(j=0;j<M;j++)
    {
//        printf("\n%d:%d %d\n",i,heap[i][1]->pnt_add,address[i]);
//        assert(heap[i][1]->pnt_add == address[i]);
        i=randlst[j];
        if(heap[i][1]->pnt_add == address[i]){
            if(heap[i][0]->p_weight==2) temp=2;
            else
                temp=(heap[i][2]->p_weight>heap[i][3]->p_weight)?2:3;
        }
        else temp=1;
        desw=heap[i][temp]->p_weight;
        desadd=heap[i][temp]->pnt_add;
        if(ans[address[i]][0]>1&&desw<0) {
            temp=0;
            desadd=index[K];
            desw=0;
        }
        tempinc=desw-p[i][address[i]];
        if(tempinc+new_cost>best_temp)
        {
            tempt=temp;
            return i;
        }
//        if(IsTabu(i,desadd)) count++;
        if(((bestinc<tempinc)&&(IsTabu(i,desadd)==0))||(tempinc+new_cost>best_cost))
        {
            bestinc=tempinc;
            point=i;
            tempt=temp;
//            printf("^^^^^%d %d %d %d %d %d\n",i,address[i],desadd,lastfrom,lastto,IsTabu(i,desadd));
        }
    }
//    printf("     Tabunum:%d\n",count);
    if(bestinc == INF) return -1;
    return point;
}

void MakeMove(int point,int p_add,int des_add)
{
    assert(p_add!=des_add);
    finalmovenum++;
    int i,j,len=ans[p_add][0];
//    countnum++;
//    printf("%d %d %d\n",point,p_add,des_add);
////    assert(address[point]==p_add);
//    for(i=0;i<K;i++) {printf("%d ",ans[i][0]);}
//    printf("\n");
//    assert(countsum==10000);
    new_cost+=(p[point][des_add]-p[point][p_add]);
//    if(des_add==K) printf("^^^^%d %d %d\n",new_cost,p[point][des_add],p[point][p_add]);
//    FILE* f=fopen("out.txt","a+");
//    fprintf(f,"**************%d\n",N);
//    for(i=0;i<N;i++){
////        printf("%d ",i);
//        for(j=1;j<=heap[i][0]->p_weight;j++){
//            if(heap[i][j]->p_weight!=p[i][heap[i][j]->pnt_add]){
//                printf("***%d %d %d %d\n",i,heap[i][j]->pnt_add,heap[i][j]->p_weight,p[i][heap[i][j]->pnt_add]);
////                getchar();
//            }
//            assert(heap[i][j]->p_weight==p[i][heap[i][j]->pnt_add]);
////        fprintf(f,"\n");
//        }
//    }
//    fclose(f);
    for(i=1;i<len;i++)
        if(ans[p_add][i]==point)
        {
            ans[p_add][i]=ans[p_add][len];
            break;
        }
    ans[p_add][0]--;
    ans[des_add][++ans[des_add][0]]=point;
//    if(des_add==K) printf(" %d  ",ans[des_add][0]);
    for(i=0;i<N;i++)
    {
        if(i==point) continue;
        p[i][p_add]-=weight[i][point];
        p[i][des_add]+=weight[i][point];
//    printf("   %d %d\n",p[i][p_add],p[i][des_add]);
//        printf("1 %d %d %d\n",i,p[i][p_add],p_add);
        p_change(i,p[i][p_add],p_add);
//        printf("2\n");
        if(ans[des_add][0]>1){
//            printf("1-1 %d %d %d\n",i,p[i][des_add],des_add);
            p_change(i,p[i][des_add],des_add);
//        printf("1-2\n");
        }
//        printf("3\n");
    }
    address[point]=des_add;
    if(ans[p_add][0]==0)
    {
//        printf("1");
//    FILE* file=fopen("out.txt","w");
//    fprintf(file,"%d %d\n",p_add,N);
//    for(i=0;i<N;i++){
//        fprintf(file,"%d ",address[i]);
////        for(j=1;j<=heap[i][0]->p_weight;j++)
////            fprintf(file,"%d ",heap[i][j]->pnt_add);
//    }
//        fprintf(file,"\n");
//    fclose(file);
        for(i=0;i<N;i++)
            p_delete(i,p_add);
        K--;
        if(backindex[p_add]!=K){
            i=index[K];
            index[backindex[p_add]]=index[K];
            index[K]=p_add;
            backindex[i]=backindex[p_add];
            backindex[p_add]=K;
//            for(i=0;i<N;i++)
//            {
////                assert(p[i][p_add]==0);
//                if(address[i]==K) address[i]=p_add;
//                for(j=1;j<=heap[i][0]->p_weight;j++)
//                    if(heap[i][j]->pnt_add==K)
//                        heap[i][j]->pnt_add=p_add;
//                p[i][p_add]=p[i][K];
//                p[i][K]=0;
//            }
//            for(i=0;i<=ans[K][0];i++)
//                ans[p_add][i]=ans[K][i];
//            ans[K][0]=0;
//            hashcluster[p_add]=hashcluster[K];
//            hashcluster[K]=0;
//        p_insert(i,0,K);
        }
    }
    if(ans[des_add][0]==1)
    {
//        printf("2");
//        p_delete(i,K);
//        printf("here\n");
//        K++;
        for(i=0;i<N;i++)
            p_insert(i,p[i][des_add],des_add);
    }
//    printf("\n");
}

void Check()
{
    int i,j,k,temp=0;
    for(i=0;i<K;i++)
    {
        for(j=1;j<ans[index[i]][0];j++)
        {
            for(k=j+1;k<=ans[index[i]][0];k++)
                temp+=weight[ans[index[i]][j]][ans[index[i]][k]];
        }
    }
//    printf("^^%d %d\n",temp,new_cost);
    assert(temp==new_cost);
}

void TabuSearch()
{
    int i,j,find,temp,add_temp,temphash;
    int non_improve=0;
    lastfrom=-1,lastto=-1;
    best_temp=new_cost;
//    for(i=0;i<HASHNUM;i++)
//        newtabu[i]=0;
    for(i=0;i<MAXK;i++)
    {
        hashcluster[index[i]]=0;
        for(j=1;j<=ans[index[i]][0];j++)
            hashcluster[index[i]]=(hashcluster[index[i]]+hashZ[ans[index[i]][j]])%HASHNUM;
//        newtabu[hashcluster[index[i]]]++;
    }
//    clustertabu[new_cost]++;
    while(non_improve<Tabucircle)
    {
        find=findBestMove(temp);
//        perturbnum[find]++;
        if(find == -1)
        {
            printf("...\n");
			return ;
        }
/*/
        add_temp=address[find];
        temphash=0;
        for(i=1;i<=ans[add_temp][0];i++)
        {
            if(ans[add_temp][i]==find) continue;
            temphash=(temphash+hashZ[ans[add_temp][i]])%HASHNUM;
        }
        tabu[find][address[find]]=temphash;
        lastfrom=add_temp;
        if(temp!=0){
        lastto=heap[find][temp]->pnt_add;
        }
        else lastto=K++;
        temphash=0;
        for(i=1;i<=ans[lastto][0];i++)
        {
            if(ans[lastto][i]==find) continue;
            temphash=(temphash+hashZ[ans[lastto][i]])%HASHNUM;
        }
        tabuO[find][lastto]=temphash;
/*/
        lastfrom=address[find];
        if(temp!=0){
            lastto=heap[find][temp]->pnt_add;
        }
        else {lastto=index[K];K++;}
        hashcluster[lastfrom]=(hashcluster[lastfrom]+HASHNUM-hashZ[find])%HASHNUM;
        hashcluster[lastto]=(hashcluster[lastto]+hashZ[find])%HASHNUM;
        if(best_temp<new_cost){
            best_temp=new_cost;
            non_improve=0;
        }
//        else{
            tabu[find][lastfrom]=hashcluster[lastfrom];
            tabuO[find][lastto]=hashcluster[lastto];
//        }
//*/
        MakeMove(find,lastfrom,lastto);
//        printf("%d %d %d %d\n",find,backindex[lastfrom],backindex[lastto],K);
        pointmovenum[find]++;
        non_improve++;
//        clustertabu[new_cost]++;
//            newtabu[hashcluster[lastfrom]]++;
//            newtabu[hashcluster[lastto]]++;
        if(new_cost>best_cost)
        {
            Check();
            best_cost=new_cost;
            bestcircle=circle;
        s2=time(NULL);
        best_time=s2-s1;
        rewritebest();
            improvenum++;
        }
    }
    return ;
}

//*随机选择一部分点重新投扰动
void Perturb()
{
    int i,j,tempi,tempj,movenum,desadd;
//    printf("T:%d %d\n",new_cost,best_cost);
    for(i=0;i<N;i++)
    {
        movepoint[i].moved=(p[i][address[i]]+BASENUM*ans[address[i]][0])*100.0/sumweight[i];
        movepoint[i].pointnum=i;
    }
    qsort(movepoint,N,sizeof(pnt_move),cmp);
//    printf("^^^%d\n",K);
    movenum=rand()%((int)(param_beta*N)-(int)(param_alpha*N))+(int)(param_alpha*N);
    if(perturbflag) {movenum=rand()%((int)(0.9*N)-(int)(param_beta*N))+(int)(param_beta*N);perturbflag=0;}
    for(j=0;j<movenum;j++)
    {
//        printf("%d ",movepoint[i].pointnum);
        i=j;
        if(circle>1000)
        {
            i=(circle/100)%2==0?i:N-j-1;
        }
//        perturbnum[movepoint[i].pointnum]++;
        while(1)
        {
            desadd=rand()%(K+1);
            if(index[desadd]==address[movepoint[i].pointnum]||(desadd==K&&ans[address[movepoint[i].pointnum]][0]==1)) continue;
            else break;
        }
        if(desadd==K)
        {
            K++;
        }
        MakeMove(movepoint[i].pointnum,address[movepoint[i].pointnum],index[desadd]);
    }
}

/*/
//拆开局部性影响最大的两个团
void Perturb()
{
    int i,j,movenum,desadd,k1=INF,k2=INF,i1,i2;
    movenum=rand()%((int)(param_beta*N)-(int)(param_alpha*N))+(int)(param_alpha*N);
    for(i=0;i<K;i++)
    {
        if(ans[i][0]>k1) {
            k2=k1,k1=ans[i][0];
            i2=i1,i1=i;
        }
        else if(ans[i][0]>k2)
        {
            k2=ans[i][0];
            i2=i;
        }
    }
    for(j=0;j<movenum/2;j++)
    {
        if(ans[i1][0]==1) break;
        desadd=rand()%K;
        if(i1==desadd)
            continue;
        MakeMove(ans[i1][rand()%(ans[i1][0])+1],i1,desadd);
    }
    for(j=0;j<movenum/2;j++)
    {
        if(ans[i2][0]==1) break;
        desadd=rand()%K;
        if(i2==desadd)
            continue;
        MakeMove(ans[i2][rand()%(ans[i2][0])+1],i2,desadd);
    }
}
//*/

/*
//移动参与move次数最少的点(效果差）
void Perturb()
{
    int i,j,tempi,tempj,movenum,desadd;
//    printf("T:%d %d\n",new_cost,best_cost);
    for(i=0;i<N;i++)
    {
        movepoint2[i].moved=pointmovenum[i];
        pointmovenum[i]=0;
        movepoint2[i].pointnum=i;
    }
    qsort(movepoint2,N,sizeof(pnt_move2),comp);
//    for(i=0;i<N;i++)
//    {
//        printf("%d %d\t",movepoint2[i].pointnum,movepoint2[i].moved);
//    }
//    printf("^^^%d\n",K);
    movenum=rand()%((int)(param_beta*N)-(int)(param_alpha*N))+(int)(param_alpha*N);
    for(j=0;j<movenum;j++)
    {
//        printf("%d ",movepoint[i].pointnum);
        i=j;
        if(circle>1000)
        {
            i=(circle/100)%2==0?i:N-j-1;
        }
//        perturbnum[movepoint[i].pointnum]++;
        while(1)
        {
            desadd=rand()%(K+1);
            if(desadd==address[movepoint[i].pointnum]||(desadd==K&&ans[address[movepoint[i].pointnum]][0]==1)) continue;
            else break;
        }
        if(desadd==K)
        {
            K++;
        }
        MakeMove(movepoint[i].pointnum,address[movepoint[i].pointnum],desadd);
    }
}
*/

void restart()
{
    int i,j,temp1,temp;
	s1=time((time_t*)NULL);
    FILE *fp=fopen("in-sol.txt","r");
//    FILE *f=fopen("out.txt","w");
    printf("restart\n");
    for(i=0;i<N;i++){
        ans[i][0]=0;
        for(j=0;j<N;j++)
        {
            p[i][j]=0;
        }
    }
    K=0;
    for(i=0;i<N;i++)
    {
        fscanf(fp,"%d",&temp);
        if(temp>=K) K=temp+1;
//        printf("%d ",temp);
        ans[temp][++ans[temp][0]]=i;
        address[i]=temp;
    }
    pre_com_hash();
    for(i=0;i<N;i++)
        for(j=0;j<MAXK;j++){
            tabu[i][j]=0;
            tabuO[i][j]=0;
        }
    for(i=0;i<=N;i++)
        for(j=0;j<K;j++)
        {
            p[i][j]=0;
            for(temp1=1;temp1<=ans[j][0];temp1++)
            {
                p[i][j]+=weight[i][ans[j][temp1]];
            }
        }
//    printf("part3\n");
    for(i=0;i<N;i++)
    {
        free(heap[i][0]);
        heap[i][0]=(pnt_heap *)malloc(sizeof(pnt_heap));
        heap[i][0]->p_weight=0;
        heap[i][0]->pnt_add=address[i];
        for(j=0;j<K;j++)
        {
            p_insert(i,p[i][j],j);
        }
    }
//    printf("part4\n");
    new_cost=0;
//    for(i=0;i<N;i++){
//        for(j=0;j<N;j++)
//            printf("%d ",weight[i][j]);
//        printf("\n");
//    }
    for(i=0;i<K;i++)
    {
        for(j=1;j<ans[i][0];j++)
        {
            for(temp1=j+1;temp1<=ans[i][0];temp1++)
            {
                new_cost+=weight[ans[i][j]][ans[i][temp1]];
            }
        }
    }
//    best_cost=(best_cost>new_cost)?best_cost:new_cost;
    if(new_cost>best_cost){
        best_cost=new_cost;
        bestcircle=circle;
        rewritebest();
//        printf("%d\n",best_cost);
    }
    printf("%d %d\n",new_cost,best_cost);
//    printf("%d\n",N);
}

int main(/*int argc, char **argv*/)
{
    int i,j,k,tempcost=0,tabuornot,perturbornot;
    circle=0;
//    randlst = new int[N];
//    for (i = 0; i < argc; i++){
//		fprintf(stdout, "%s ", argv[i]);
//	}
//	fprintf(stdout, "\n");
//	for (i = 1; i < argc; i+=2){
//		if (argv[i][0] != '-' || argv[i][2] != 0){
//			showUsage();
//			exit(0);
//		}else if (argv[i][1] == 'f'){
//			strncpy(param_filename, argv[i+1],1000);
//		}else if (argv[i][1] == 's'){
//			MAXTIME = atoi(argv[i+1]);
//		}else if(argv[i][1] == 'a'){
//			param_alpha = atof(argv[i+1]);
//		}else if (argv[i][1] == 'b'){
//			param_beta =  atof(argv[i+1]);
//		}else if (argv[i][1] == 't'){
//			Tabucircle = atoi(argv[i+1]);
//		}
//	}
//	/*check parameters*/
//	if (strlen(param_filename) == 0){
//		cerr << "No input data" << endl;
//		exit(1);
//	}
//	printf("%s\n",param_filename);

//    char s[]="charon_busco\\rand500-100.txt";
//    char s[1000]="in2-300n.txt";
    char s[1000]="unif800-100-5.txt";
//	strncpy(s,param_filename,1000);
//	printf("%s\n",s);
    char buffer[200];

	s0=time((time_t*)NULL);
	ReadFile(s);
	sprintf(buffer,"best2_%s",s);
	FILE *outf=fopen(buffer,"a+");
	srand((unsigned)time(NULL));
	M=(MAXPOINT>N)?N:MAXPOINT;
	best_cost=INF;

	improvenum=0;
	Tabucircle=min(10*N,15000);
//	Tabucircle=300;
	for(i=0;i<N;i++)
	{
	    sumweight[i]=0;
	    pointmovenum[i]=0;
	    for(j=0;j<N;j++)
	    {
	        sumweight[i]+=weight[i][j]+BASENUM;
	    }
	}
	finalmovenum=0;
	timetemp=0;
        s2=time((time_t*)NULL);

    while((s2-s0)<MAXTIME)
    {
//*自己初始化
    InitialSolution2();
    s3=time((time_t*)NULL);
/*/
//使用聚类的初始化
	restart();
//*/

//	for(i=0;i<HASHNUM2;i++)
//        clustertabu[i]=0;
	while(circle<MAXCIRCLE)
	{
	srand((unsigned)time(NULL));
//	    printf("Started\n");
//	    if(circle==MAXCIRCLE/2) restart();
//	    tabuornot=DescentSearch();
//	    printf("DescentSearch Done\n");
//	    if(tabuornot){
            TabuSearch();
            T1=new_cost;
//            printf("TabuSearch Done\n");
//	    printf("T:%d %d %d %d   ",K,best_temp,new_cost,best_cost);
//	    }
//	    if(circle%3==0)
//        if(circle%10==0){
//            perturbflag=1;
//            Perturb();
//        }
        Perturb();
//        if(K>=3&&(circle+1)%100==0) {
//            lastc1=-1,lastc2=-1;
//            backtobest();
////            printf("Tabu2 start\n");
//            TabuSearch2();
////            printf("Tabu2 success\n");
//            T2=new_cost;
//        }
//	    else
//            printf("Tabu2 Success.\n");
//	    printf("Perturb Done\n");
//	    printf("P:%d %d %d\n",K,new_cost,best_cost);
	    circle++;
        s2=time((time_t*)NULL);
        if(s2-s0>MAXTIME) break;
        if(s2-s3>(BASETIME*restarttime[timetemp])) break;
//        if(s2-s1>20&&s2-s1>MIN(25+best_time,5*best_time)) restart();
//        printf("%d %d %d\t\t\t",best_cost,T1,T2);
	}
        timetemp++;
        s2=time((time_t*)NULL);
    }
    int tempk=0;
	for(i=0;i<N;i++){
	    tempk=(tempk>=bestaddress[i])?tempk:bestaddress[i];
	}
	for(i=0;i<=MAXK;i++){
        ans[i][0]=0;
        index[i]=bestindex[i];
	}
	for(i=0;i<N;i++){
	    ans[bestaddress[i]][++ans[bestaddress[i]][0]]=i;
	}
	s2=time((time_t*)NULL);

    for(i=0;i<=tempk;i++)
    {
        for(j=1;j<ans[index[i]][0];j++)
        {
            for(k=j+1;k<=ans[index[i]][0];k++)
                tempcost+=weight[ans[index[i]][j]][ans[index[i]][k]];
        }
    }

	assert(tempcost==best_cost);
	printf("^^^ %d %d %d\n",best_cost,bestcircle,best_time);
    fprintf(outf,"%d %d %d\n",best_cost,bestcircle,best_time);
    for(i=0;i<N;i++){
        fprintf(outf,"%d ",bestaddress[i]);
    }
    printf("Tabu:%d\n",improvenum);
    printf("Time:%d\n",s2-s0);
    printf("movenum:%d\n",finalmovenum);
    fprintf(outf,"\n");

    return 0;
}
