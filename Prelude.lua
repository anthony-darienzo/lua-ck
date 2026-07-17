-- Some Lua functions are useful to have at hand.
local Prelude = {}

Prelude.table = {}

function Prelude.table.with_default_meta(t, f, ...) 
    -- Call function `f` on `t`, where the metatable of `t` is temporarily
    -- altered to unset __index, __pairs. Return the result of
    -- `f(t)` after fixing the metatable back.
    --
    -- If the metatable of `t` also has a metatable, good luck!
    local mt = getmetatable(t)
    local i
    local p
    if mt then
        if mt.__index then
            i = mt.__index
            mt.__index = nil
        end
        if mt.__pairs then
            p = mt.__pairs
            mt.__pairs = nil
        end
    end

    local res = f(t, ...)

    if mt then
        mt.__index = i
        mt.__pairs = p
    end

    return res
end

-- In the following functions, `ms` is a table whose k,v pairs are:
--   k : a table/subtable of the input to a deepcopy.
--   v : the associated duplicate subtable under construction.
--
-- ms is modified in place! Returns it anyways.
local function Prelude_table_vertices_helper (t, ms)
    ms = ms or {}
    if not ms[t] then ms[t] = {} end
    for _, v in pairs(t) do
        if type(v) == "table" and not ms[v] then
            ms[v] = {}
            -- Populate ms with the vertices of v now.
            Prelude.table.vertices(v, ms)
        end
    end
    return ms
end

function Prelude.table.vertices (t, ms)
    -- Find vertices of the epsilon-graph of t, i.e., the subtables of t.
    return Prelude.table.with_default_meta(t, Prelude_table_vertices_helper, ms)
end

local function Prelude_table_refgraph_helper (t, ms)
    if ms then
        Prelude.table.vertices(t,ms) -- do in place
    else
        ms = Prelude.table.vertices(t) -- generate ms
    end
    
    -- Find edges.
    local es = {}
    for s, _ in pairs(ms) do
        es[s] = {}
        for k, v in pairs(s) do
            if ms[v] then
                if not es[s][v] then
                    es[s][v] = {}
                end
                table.insert(es[s][v], k)
            end
        end
    end
    -- Now, for any pair of tables u and v, if es[u][v] is not nil, then the
    -- entry x = es[u][v] is the set of keys k such that u[k] = v
    -- 
    -- u -[k]-> v, forall _, k in pairs(x).
    return {V = ms, E = es}
end

function Prelude.table.refgraph (t, ms)
    -- Every lua table is a connected multigraph. Return that graph.
    -- The vertices are tables and subtables. A directed edge v1 -[k]-> v2 exists if
    -- v1[k] = v2.
    
    return Prelude.table.with_default_meta(t, Prelude_table_refgraph_helper, ms)
end

function Prelude.table.dc (t, ms)
    -- Deep copy a Lua table, preserving cyclic references.
    --
    -- If there is a k,v pair t[k] = v, where k is a table, then:
    --   1. If k is a subtabe of t, we duplicate k and use this duplicate in the
    --      deep copy.
    --   2. If k is not a subtable of t, we use the same k in the deep copy.
    --
    -- All subtables are deep copied.
    --
    -- If ms is provided, store the intermediate new tables here. This will
    -- allow us to also deep copy the metatable of t.
    --
    ms = ms or {}

    local Gt = Prelude.table.refgraph(t, ms)
    -- At this point, as we range over the keys k of ms, ms[k] is the table
    -- representing the duplicate of `k`. In particular, eventually `ms[t]` will
    -- be the deep copy of `t`!
    local es = Gt.E

    -- Now we loop through the edges to attach the references.
    -- Any time we find an edge v1 -[k]-> v2, we want to introduce a new
    -- reference:
    --
    -- 1. ms[v1] -[k]-> ms[v2] if not ms[k]
    -- 2. ms[v1] -[ms[k]]-> ms[v2] if ms[k]
    for v1, v1t in pairs(es) do
        for v2, ks in pairs(v1t) do
            -- Note ks = es[v1][v2]
            for _, k in pairs(ks) do
                if ms[k] then
                    -- The key is a subtable! Point via the new one.
                    ms[v1][ ms[k] ] = ms[v2]
                else
                    -- The key is not a subtable. It could be another "external"
                    -- table or a different type. Use it verbatim.
                    ms[v1][k] = ms[v2]
                end
            end
        end
    end

    -- Now we should have all the cyclic subtables done. All that remains is to
    -- copy over the noncyclic data.
    for s, _ in pairs(ms) do
        -- Since s may have a custom __pairs function, we should intercept that
        -- first.
        Prelude.table.with_default_meta(s, function(x)
            for k, v in pairs(x) do
                if type(v) ~= "table" then
                    if type(k) == "table" and ms[k] then
                        ms[x][ ms[k] ] = v                
                    else
                        ms[x][k] = v
                    end
                end
            end
        end)
    end

    -- Now we need to handle the metatables.
    for s, _ in pairs(ms) do
        local s_mt = getmetatable(s)
        -- It's possible s_mt is a table we've already seen!
        if s_mt and ms[s_mt] then
            setmetatable(ms[s], ms[s_mt])
        elseif type(s_mt) == "table" then
            -- We haven't seen s_mt before. Safe to copy.
            local new_mt = Prelude.table.dc(s_mt, ms)
            setmetatable(ms[s], new_mt)
        else
            -- s_mt is either nil or a string. This informs the choice of
            -- __metatable parameter of s. Tell ms[s] to behave the same.
            setmetatable(ms[s], { __metatable = s_mt })
        end
    end

    return ms[t]
end

function Prelude.dc (x)
    -- If x is a table, deep copy it and return. Otherwise, return x.
    if type(x) ~= "table" then
        return x
    else
        return Prelude.table.dc(x)
    end
end

return Prelude
