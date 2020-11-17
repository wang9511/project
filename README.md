# H-CMP README

## 配置

- python 3.6.1

  Packages: 

  - pandas
  - sklearn
  - subprocess

- cmurphi5.4.9.1
  
  - [安装指南](https://arabelatso.github.io/2017/02/19/murphi-introduction-1/)
  
  
  
- 特别提示：

  1. 如何增大cmurphi能验证的invariant数量：

  - murphi默认的能够验证的invariant数目有限，一旦超出限制，则会出现stack full 的情况。若想避免该情况，在make后，手动修改`cmurphi5.4.9.1/src/y.tab.c`中的：

  -  `#define YYINITSTACKSIZE `数值改成`20000`或更多
  - `\#define YYSTACKSIZE `数值改成`100000`或更多
  - `#define YYMAXDEPTH  100000数值`改成`100000`或更多

  2. 如何在遇到反例之后继续运行：

  - `cmurphi5.4.9.1/include/murphi.original/mu_system.cpp`的`PropertyManager::CheckInvariants()`:

    ```c
    bool PropertyManager::CheckInvariants()
    {
      category = INVARIANT;
      if (!args->find_errors.value){
        for (what_invariant = 0; what_invariant < numinvariants; what_invariant++) 
        {
          if (!(*invariants[what_invariant].condition) ())
          {
            return FALSE;
          }
        }
      }
      else{
        for (what_invariant = 0; what_invariant < numinvariants;
            what_invariant++) {
          if (find(failed_invs.begin(),failed_invs.end(),what_invariant)!=failed_invs.end()){
              // if this invariant has already failed in previous states, then skip it.
              continue;
          }
          else if (!(*invariants[what_invariant].condition) ())
            /* Uh oh, invariant blown. */
          {
            failed_invs.push_back(what_invariant);
            cout << "Invariant \""<< Properties->LastInvariantName()<<"\" failed.\n";
          }
        }
      }
      return TRUE;
    }
    ```

    之后就可以正常使用`-finderrors` 这个参数了（原来的cmurphi中虽然设置了这个参数，但没有实现）= =|||



## 使用方式

### Run shell file

这个方法可以在linux/Mac OS上运行，windows用户参见下面【完整过程】

（确保 `murphi_url.txt` 中填写正确）



```shell
pip install -r requirements.txt
./run.sh
```



### 完整过程

#### 预设

- 待验证的协议（如mutualEx.m）的文件夹，文件夹与协议同名
- 写入murphi路径至`murphi_url.txt`文件中

#### 输入

```shell
python3 main.py -p mutdata -a NODE -n 2 -all -r y
```

#### 参数

- Optional arguments:
    -h, --help            show this help message and exit
    -all, --all           'all': go through all options in L-CMP (default:
                          False)
    -pre, --preprocess    'preprocess': calculate reachable set only (default:
                          False)
    -l, --learn           'learn': learn auxiliary invariants only (default:
                          False)
    -cmp, --cmp           'cmp': conduct cmp only (default: False)
    -p PROTOCOL, --protocol PROTOCOL
                          Name of the protocol under verification. (default:
                          None)
    -a ABS_OBJ, --abs_obj ABS_OBJ
                          Object under abstraction (default: NODE)
    -n NODE_NUM, --node_num NODE_NUM
                          Number of normal nodes (default: 2)
    -k KMAX, --kmax KMAX  Max size of frequent itemset (default: 3)
    -s SUPPORT, --support SUPPORT
                          Minimum support threshold (default: 0.0)
    -c CONFIDENCE, --confidence CONFIDENCE
                          Minimum confidence threshold (default: 1.0)
    -i ITER, --iter ITER  Max iteration of strengthening (default: 2)
    -src SRCFILE, --srcfile SRCFILE
                          Path to the protocol under verification. (default:
                          None)
    -out OUTPUTFILE, --outputfile OUTPUTFILE
                          Path to the destination protocol. (default: None)
    -r {y,n}, --recalculate {y,n}
                          Whether recalculate all the support files. (default:
                          n)

#### 输出

- 可达集 (`mutualEx.txt`,`mutualEx.csv`,`trans_dataset.csv`)
- 收集到的原始原子公式集（collected_atom.txt）——可作为原子公式集的参考，但不能作为最终的原子公式集
- 关联规则集 (`assoRules.txt`)
- 辅助不变式（`aux_invs.txt`）
- 用到的辅助不变式(`used_aux_invs.txt`)
- 加强抽象后的协议(不含辅助不变式：`ABS_mutualEx.m`， 含辅助不变式：`ABS_mutualEx_1.m`) 
- 记录文档，记录抽象过程(`prot.abs`)



#### 注意

- 小型协议的计算过程迅速，大型协议则较慢

- 必须给定的参数：
  -  `-p` (指定协议名称)
  -  `-a` （指定抽象的对象，如结点NODE)
- 可给定的参数：
  - `-n` 指定抽象协议中普通结点的个数，默认为2. 如验证FLASH协议，则需设置为3.
  - `-r` 默认为

### 根据公式，计算辅助不变式

#### 预设

在python文件中给出协议名称及待验证的表达式，形如`!(n[1] = C & x = true)` 

#### 输入

```
python3 decide_formula.py
```

#### 输出

辅助不变式集合

#### 注意

- 表达式中的符号需与协议计算出的可达集符号一致，即，当表达式中以实数作为下标，则协议文件夹中的协议也必须对应为<u>非对称规约</u>的形式；当表达式中以符号作为下标，则协议文件夹中的协议也必须对应为<u>对称规约</u>的形式
- 当对协议进行过修改之后，需手动删除协议文件夹中的 `协议名.txt` 及`协议名.csv`文件，以保证协议与可达集的对应关系

## 文件介绍

### python文件

- `main.py` ：主函数

- `preprocess.py ` ：
  - 数据预处理 (DataProcess)
  - 关联规则学习 (RuleLearing)
  - 辅助不变式筛选(SlctInv)
- `analyser.py` : 
  - 分析协议
    - 收集原子公式（collect_atoms）
    - 抽象与加强（refine_abstract）

### 协议文件夹

- 每个协议放在协议同名的文件夹下，如mutualEX协议（`mutualEX.m`）放置在mutualEX文件夹内
- 每个协议的文件夹内默认有一个`atom.txt` 文件，用于存放原子公式
- 如果没有提供原子公式，则自动将可达集中出现的赋值（如 `n[NODE_1].state = C`）及其取反（如 `n[NODE_1].state ！= C`）作为原子公式集
- **注意**：原子公式的形式需与协议生成的可达集对应，即当可达集采取对称规约时，原子公式的形式也应形如`n[NODE_1].state = C` (以`NODE_1`等符号作为下标)；当可达集未采取对称规约时，则原子公式形如`n[1].state = C` (以`1`等实数作为下标)

### murphi路径

文件`murphi_url.txt`用于存放murphi路径，比如`../../Documents/Lab/cmurphi5.4.9.1/`

## 主函数框架

```
try:
		接收各种参数，并检查参数的有效性
except:
  	输出help 信息，退出程序
else：
		输出验证信息（协议名称、参数列表）
		计算可达集，如有，则跳过
		分析协议，收集原子公式
		if 文件夹中已经有辅助不变式集合：
			读入辅助不变式
		else:
				if 文件夹中已经有关联规则集合：
					读入关联规则
    		else: 
    			对数据集进行编码
    			筛选出全局变量
    			关联规则计算，并在计算频繁集时排除全是全局变量的频繁集
    
    		筛选出能被迁移规则的guard蕴含的关联规则
   		 	对称缩减、去除冗余
    		翻译成murphi语言，并用murphi进行筛选
    		删掉无法通过检测的关联规则，得到辅助不变式集合
  
    抽象及验证
    将用到的辅助不变式也加入抽象协议，并用Murphi进行模型检测
    if 有反例：
    		while 有反例 & 循环次数小于10:
    				删除反例
    				抽象及验证
    				将用到的辅助不变式也加入抽象协议，并用Murphi进行模型检测
    		if 有反例:
    				输出反例序号
    else:
    		验证结束
    		
    记录时间信息
```