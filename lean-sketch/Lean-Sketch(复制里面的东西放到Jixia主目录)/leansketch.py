import json
import extractgraph
import analyze_graph
import prompt
from pyvis.network import Network
import subprocess
import os

elab_graph = {}   #key:module.{string position} value:dict with value:'child':list of subnodes 'label':node name，'isConstant':bool.

module_dep = {}     #key:module   value:dict，'parent':any module that has key as a constant. For using JIXIA to find module path.

is_dep = {}

important = {}

main_module = ""

whitelist = []

#variables for prompting LLMs
constant_definition = {}    #get interested constant list
module_dependency = {}      #get module dependency tree


def run_jixia(file_path, module_name): 
    if not os.path.isfile("./tmp/tmp." + module_name + ".lean"):
        with open(file_path, "r", encoding='utf-8') as source_file:
            with open("./tmp/tmp."+ module_name + ".lean" , "w", encoding='utf-8') as target_file:
                for line in source_file.readlines():
                    target_file.write(line)
    
    initial = "lake env lean -o ./"+ module_name + ".olean ./tmp/tmp."+ module_name +".lean"
    if not os.path.isfile("./tmp/" + module_name +".olean"):
        print("running：",initial)
    subprocess.run(initial)
    run_flag = False
    if not os.path.isfile("./tmp/" + module_name + ".sym.json"):run_flag = True
    if not os.path.isfile("./tmp/" + module_name + ".decl.json"):run_flag = True
    if not os.path.isfile("./tmp/" + module_name + ".elab.json"):run_flag = True
    if not os.path.isfile("./tmp/" + module_name + ".lines.json"):run_flag = True
    command = "lake env ./.lake/build/bin/jixia -i -d ./tmp/"+ module_name +".decl.json -s ./tmp/"+module_name+".sym.json -e ./tmp/"+ module_name +".elab.json -l ./tmp/"+ module_name +".lines.json "+file_path
    if run_flag: subprocess.run(command)  
    # command = "lake env ./.lake/build/bin/jixia -i -s ./tmp/"+module_name+".sym.json "+file_path 
    # if run_flag: subprocess.run(command)  
       
        

def get_module(const,module):      
    file_path = "./tmp/"+ module + ".sym.json"
    with open(file_path, 'r', encoding='utf-8') as f:
        sym = json.load(f)
    for d in sym:
        valuemod = d["valueModules"][0]
        flag = False
        for c in valuemod:
            if c.endswith(const)and (c==const or c[-(len(const))-1]=='.'):
                flag = True
                break
        if flag and valuemod[c][0]!=None:
            mod = valuemod[c][0]
            mod_name = mod[0]
            for i in range(1,len(mod)):
                mod_name = mod_name + '.' + str(mod[i])
            return mod_name

def module_to_file(module,parent):   
    if module==main_module:
        file_path = "./"+main_module+".lean"
        return file_path    
    sym_path = "./tmp/"+ parent + ".sym.json"
    with open(sym_path, 'r', encoding='utf-8') as f:
        sym = json.load(f)
    for d in sym:
        for const in d["valueModules"][0]:
            m = d["valueModules"][0][const][0]
            if m == None: continue
            module_name = m[0]
            for i in range(1,len(m)):
                module_name = module_name + '.' + str(m[i])
            if module_name==module:
                file_path = d["valueModules"][0][const][1]
                return file_path
     

def get_constants(file_path):        
    constants = []
    with open(file_path, 'r', encoding='utf-8') as f:
        sym = json.load(f)
    for d in sym:
        if d["valueReferences"] is not None:
            for const in d["valueReferences"]:
                if len(const)==0: continue
                constant_name = const[0]
                for i in range(1,len(const)):
                    constant_name = constant_name + '.' + str(const[i])
                if constant_name not in constants:
                    constants.append(constant_name)
        if d["typeReferences"] is not None:
            for const in d["typeReferences"]:
                if len(const)==0: continue
                constant_name = const[0]
                for i in range(1,len(const)):
                    constant_name = constant_name + '.' + str(const[i])
                if constant_name not in constants:
                    constants.append(constant_name)
        c = d['name']
        constant_name = c[0]
        for i in range(1,len(c)):
            constant_name = constant_name + '.' + str(c[i])
        if constant_name not in constants:
            constants.append(constant_name)
    return constants
            


def analyze_constant(dg):         #return a list of interested constant, adding to "constants_toget"
    constant_list = []           
    for node in dg:
        while node in dg[node]['child']:dg[node]['child'].remove(node)
        if is_dep[node] and dg[node]['child']==[] and dg[node]['isConstant']:
            constant_list.append(dg[node]['label'])
            #print("Extending node :",node,dg[node]['label'],".")
    return constant_list          #a single constant can have many nodes
    
def get_dep(node,dg):
    global is_dep
    for child in dg[node]['child']:
        if is_dep[child]==False:
            is_dep[child] = True
            get_dep(child,dg)   
    
def analyze_elab_node(constant,dg):
    visited = {}
    constant_in_code = constant.split('.')[-1]
    for node in dg:
        visited[node] = False
    for node in dg:
        if constant_in_code in dg[node]['label'] and dg[node]['child']!=[]:
            start = node
            break
    tr = start
    while(True):
        flag = False
        for node in dg:
            if tr in dg[node]['child'] and not visited[node]:
                visited[node] = True
                tr = node
                flag = True
                break
        if not flag: break
    return tr            
    
def interested(module):
    if whitelist==[]: return True
    if module == main_module: return True
    for m in whitelist:
        if len(m)>len(module):continue
        if m in module: return True
    return False

def build_graph():
    global elab_graph
    global is_dep
    
    global constant_definition
    
    constants_extended = []          #key:module   value:constants  level i+1 module <--> level i constant
    nodes_extended = []              #value:dict     its ith value: level i constant's nodes                   
    module_level = []                #value:list     

    for i in range(0,level+1): module_level.append([])
    for i in range(0,level+1): nodes_extended.append({})
    for i in range(0,level+1): constants_extended.append({})
    module_level[0].append(main_module)
    module_dep[main_module]={}
    module_dep[main_module]['parent']=""
    
    for i in range(0, level):
        for module in module_level[i]:            
            if not interested(module) and i!=0: continue
            print("__________________________________________________________")
            print("Level i=",i,". Analyzing module:",module)
            
            if i!=0 : print("Constants:",constants_extended[i][module])
    
            run_jixia(module_to_file(module,module_dep[module]['parent']),module)
            path = "./tmp/"+ module + ".elab.json"
            dg = extractgraph.ExtractGraph(path,module)
            path = "./tmp/"+ module + ".sym.json"
            constants = get_constants(path)
            
            pure_constants = []
            for c in constants:
                pure_constants.append(c.rsplit('.', 1)[-1])
                
            for node in dg:
                if dg[node]['label'].rsplit('.', 1)[-1] in pure_constants: dg[node]['isConstant'] = True
                else: dg[node]['isConstant'] = False            
            
            #glue dg to elab_graph
            #one file at a time doing:
            # 1.add new nodes 
            # 2.connect new nodes to constant nodes  keep the connection of subnodes of constants in dg
                        
            if i==0:                                                #runs once
                constants_extended[0][module] = []
                constants_extended[0][module].append(main_constant)    #module = main_module
                nodes_extended[0][main_constant]=[]
                root = analyze_elab_node(main_constant,dg)
                elab_graph[root] = {}
                elab_graph[root]['label'] = dg[root]['label']
                elab_graph[root]['child'] = []
                elab_graph[root]['isConstant'] = False
                nodes_extended[0][main_constant].append(root)
        
            is_dep.clear()
            ii = 0
            for node in dg:
                ii = ii+1
                is_dep[node] = False
            for root_node_constant in constants_extended[i][module]:
                r = analyze_elab_node(root_node_constant,dg)
                get_dep(r,dg)                  
                
                ###################FOR LLM############################### 
                if root_node_constant not in constant_definition:
                    constant_definition[root_node_constant] = dg[r]['label']
                #########################################################
                                
            for node in dg:
                if is_dep[node] and (node not in elab_graph):
                    elab_graph[node] = {}
                    elab_graph[node]['label'] = dg[node]['label']
                    elab_graph[node]['child'] = dg[node]['child']
                    elab_graph[node]['isConstant'] = dg[node]['isConstant']

            for root_node_constant in constants_extended[i][module]:
                for n in nodes_extended[i][root_node_constant]:
                    connect_root = analyze_elab_node(root_node_constant,dg)
                    for children in dg[connect_root]['child']:
                        elab_graph[n]['child'].append(children)

            #################################################      preparing for i+1
            constants_dg = analyze_constant(dg)              
            for const in constants_dg:
                            
                if const == None:continue
                for node in dg:
                    if dg[node]['label'].rsplit('.', 1)[-1] == const.rsplit('.', 1)[-1] and dg[node]['child']==[] and is_dep[node]:
                        if const not in nodes_extended[i+1]:nodes_extended[i+1][const]=[] 
                        nodes_extended[i+1][const].append(node)
            for const in nodes_extended[i+1]:
                m = get_module(const,module)                
                if m==None: continue    
                if const == None:continue            
                if m not in module_level[i+1]: 
                    module_level[i+1].append(m)
                    print("Const '",const,"' opens module:",m,".")
                    module_dep[m]={}
                    module_dep[m]['parent'] = module
                    if m not in constants_extended[i+1]: constants_extended[i+1][m] = []
                if const not in constants_extended[i+1][m]: 
                    constants_extended[i+1][m].append(const)                         
                
            #################################################
        print("-----------------------------")
        print("In next round these constants and nodes will be extended:\n",nodes_extended[i+1])
        print("These modules:\n",module_level[i+1])                
 
 

def save_knowledge_base():
    with open('kb.md', 'w', encoding='utf-8') as f:
        for constant in constant_definition:
            print(constant + ":\n",file = f)
            print(constant_definition[constant] + "\n\n",file = f)
        
#------------------FOR DEBUG----------------------        
        
def visualize(dg):
    node_id = 0
    id_dict = {}
    net = Network(height='750px', width='100%', directed=True)
    for node in dg:
        node_id = node_id + 1
        net.add_node(node_id, label=node+'+'+dg[node]['label']+'+'+str(dg[node]['isConstant']))
        if important[node]:
            net.get_node(node_id)['color']='green'
        id_dict[node]=node_id
    for node in dg:
        for subnode in dg[node]['child']:
            net.add_edge(id_dict[node], id_dict[subnode])
        
    net.set_options("""
    {
      "layout": {
        "hierarchical": {
          "enabled": true,
          "direction": "UD",
          "sortMethod": "directed"
        }
      },
      "physics": {
        "hierarchicalRepulsion": {
          "centralGravity": 0
        },
        "minVelocity": 0.75,
        "solver": "hierarchicalRepulsion"
      }
    }
    """)        
    net.show("./visualize.html",notebook=False)



def leansketch(module, constant, searchlevel):
    global level
    global main_module
    global main_constant
    level = searchlevel
    main_module = module
    main_constant = constant
    build_graph()
    
    
if __name__ == "__main__":
    with open('./config', 'r', encoding = 'utf-8') as f:
        p = f.read()  
    parameters = p.splitlines()
    level = int(parameters[0][6:])
    thm = parameters[1][8:]
    main_module = parameters[2][12:]
    if "True" in parameters[3]:activate_visual = True
    else: activate_visual = False

    with open('./whitelist', 'r', encoding = 'utf-8') as f:
        w = f.read()
    whitelist = w.splitlines()  

    leansketch(main_module,thm,level)
    for node in elab_graph:
        important[node] = False
        score = analyze_graph.get_score(node,elab_graph)
        if score > 3: important[node] = True
    if activate_visual: visualize(elab_graph)   
      
    ###############################################################
    for constant in constant_definition:
        print(constant,":\n")
        print(constant_definition[constant],"\n\n")
    save_knowledge_base()              #optional
    
    lemmas_raw, definitions_raw = prompt.choose_lemmas_definitions(constant_definition,thm)
    lemmas = []
    definitions = []    
    for l in lemmas_raw:
        if l in constant_definition: lemmas.append(l)
    for l in definitions_raw:
        if l in constant_definition: definitions.append(l)
    
    proof = prompt.translate(constant_definition,thm,lemmas,definitions)
    
    print("\n\n\n\n\n\n\n_______________PROOF IN NL_________________\n\n")
    print(proof)
    
    with open('proof.md', 'w', encoding='utf-8') as f:
        print(proof,file=f)