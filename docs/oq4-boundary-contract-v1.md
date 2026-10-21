# OQ4 反向分块的条件边界占据冻结 v1

源 current/oq4/b01/proof01.md §5 O0/O3/O4。复用真实KilledPathLaw、公共有限iid law/固定反序与闭生存；不假设生存条件后的独立性，不把S/AC外部概率输入当已证明。

ν任意ℝ Borel概率测度，Π_t=Measure.pi(fun _ : Fin t => ν)。l,r≥1自然数，m=l+r；h≥0、|z|≤h，j自然数。κ=(killedIterKernel ν h m) z，d(w)=h−|w|，E_j={w | j≤d(w)<j+1}（已有boundaryLayer）。

对任意t定义公共闭一侧事件 U_t(d)=Shao.closedUpper d，及L_t(d)={b | -b∈Shao.closedUpper d}；即所有0≤k≤t的前缀和分别≤d或≥−d。用实际全乘积law度量这些事件。

第一冻结结论：给定q,sPlus,sMinus≥0，若

- 对所有实x，Π_l.real{a | Shao.prefixSum a l∈[x,x+1]}≤q；
- Π_r.real(U_r(j+1))≤sPlus，Π_r.real(L_r(j+1))≤sMinus，

则实际被杀终点层满足

κ.real(E_j)≤q(sPlus+sMinus)。

证明必须保留源机制：上半末层(h−j−1,h−j]迫使末块反序前缀下界≥−(j+1)，下半末层[-h+j,-h+j+1)迫使反序前缀上界≤j+1。先在未条件化Π_l×Π_r中固定完整末块，首块端点位于某个长度1闭区间内，首块生存条件可丢弃；再用固定反序law和一侧事件概率。两层的重叠只扩大上界，原子/严格与闭端点均不得丢弃。需要的路径拼接、终点、事件、积分/测度均应实际可测。

第二冻结结论（源O0的数值约化）：m≥6，l=m/2为自然除法，r=m−l，β,Cq,Cs≥0。若上述真实概率输入分别具有界

q=Cq β/sqrt(l)，sPlus=sMinus=Cs(j+1+β)/sqrt(r)，

则κ.real(E_j)≤6 Cq Cs β(j+1+β)/m。

第三冻结结论（h²块的统一层形式）：h≥3、m=⌊h²⌋₊，0≤β≤M、M≥0，使用第二项相同的真实S/AC输入，则

κ.real(E_j)≤[12 Cq Cs M(1+M)/h²](j+1)。

每个j的输入与结论都量化清楚，可逐j供应AveragedResidual所需全部层；不得省略S/AC概率前提。β在本条件性模块只作非负参数，源实例可取实际第三绝对矩。无需额外中心/方差/矩、密度、非格点或有界支持。与源相同的iid独立性通过未条件化有限乘积或既审共同joint-law使用。

拟Shao/OQ4/BoundaryOccupation.lean。该单元关闭反向分块从明确S/AC到真实O0层质量的概率机制及安全常数，不证明S/AC本身、能量标记O1/O2、无条件O0、实际R3/R4、B1、K/Kv或OQ4。不改共同定义/既审源。
