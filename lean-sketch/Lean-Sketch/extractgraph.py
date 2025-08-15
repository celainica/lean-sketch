import json

dg = {}
module_name = ""
count = 0
count2 = 0

def build_graph(node):
    global dg
    global count
    global count2
    count2 = count2 + 1
    label = node.get('ref', {}).get('str', 'Unnamed Node')
    node_id = module_name + '.' + str(node['ref']['range'])
    if node_id not in dg:
        dg[node_id]={}
        dg[node_id]['child']=[]
        dg[node_id]['label']=label
        count = count + 1
    for child in node.get('children',[]):
        child_id = str(child['ref']['range'])
        if child_id not in dg[node_id]['child'] : dg[node_id]['child'].append(module_name+'.'+child_id)
        build_graph(child)



def ExtractGraph(file_path,name):
    global module_name
    module_name = name
    with open(file_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    dg.clear()
    
    for root_node in data:
        build_graph(root_node)
    
    print("Module ",name," node count:",count,".")
        
    return dg