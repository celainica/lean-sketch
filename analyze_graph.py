visited = {}
dg = {}


def get_child(r):
    visited[r] = True
    for node in dg[r]['child']:
        if not visited[node]:
            get_child(node)

def get_score(r,graph):
    score = 0
    global dg
    dg = graph
    for node in dg:
        visited[node] = False
    for node in dg[r]['child']:
        if not visited[node]:
            score = score +1
            get_child(node)
    return score