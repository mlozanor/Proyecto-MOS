# vrp_model.mod

# ========================
# Conjuntos
# ========================
set V;   # Vehículos
set N;   # Todos los nodos
set D within N;  # Clientes (Municipios)
set P within N;  # Depósito
set E within N;  # Estaciones

# ========================
# Parámetros
# ========================
param Ft;  # Tarifa de flete (COP/km)
param Cm;  # Costo de mantenimiento (COP/km)
param consumo;  # Consumo de combustible (galones/km)

param dist {N, N} >= 0;  # Distancia entre nodos
param Q {V} >= 0;        # Capacidad de carga del vehículo
param F_cap {V} >= 0;    # Capacidad de combustible del vehículo
param demand {D} >= 0;   # Demanda de los clientes
param fuel_price {N} >= 0;  # Precio de combustible en cada nodo

# ========================
# Variables
# ========================
var x {V, N, N} binary;         # Flujo de vehículo v de i a j
var z {V} >= 0, <= 1;           # Fracción del vehículo utilizado
var f {V, N, N} >= 0;           # Nivel de combustible en tránsito
var r {V, N} >= 0;              # Cantidad de recarga en nodo i

# Variables para eliminación de subtours (MTZ mejorado)
var u {V, N} >= 0;              # Variable de posición en la ruta

# ========================
# Función Objetivo
# ========================
minimize TotalCost:
    sum {v in V, i in N, j in N : i != j} (Ft + Cm) * dist[i,j] * x[v,i,j]
  + sum {v in V, i in N} fuel_price[i] * r[v,i];

# ========================
# Restricciones
# ========================

# R1: Cada cliente recibe flujo total de 1
subject to ClientFlow {j in D}:
    sum {v in V, i in N : i != j} x[v,i,j] = 1;

# R2: Conservación de flujo
subject to FlowConservation {v in V, k in N diff P}:
    sum {i in N : i != k} x[v,i,k] = sum {j in N : j != k} x[v,k,j];

# R3: El flujo que sale del depósito es igual a z[v]
subject to DepotOutflow {v in V}:
    sum {i in P, j in N : i != j} x[v,i,j] = z[v];

# R4: El flujo que regresa al depósito es igual a z[v]
subject to DepotInflow {v in V}:
    sum {i in N, j in P : i != j} x[v,i,j] = z[v];

# R5: Capacidad de carga del vehículo
subject to Capacity {v in V}:
    sum {j in D} demand[j] * sum {i in N : i != j} x[v,i,j] <= Q[v] * z[v];

# R6: Balance de combustible entre nodos
subject to FuelBalance {v in V, i in N, j in N : i != j}:
    f[v,i,j] >= f[v,j,j] - consumo * dist[i,j] * x[v,i,j];

# R7: Máximo de combustible permitido en un nodo
subject to MaxFuelCapacity {v in V, i in N}:
    f[v,i,i] <= F_cap[v] * sum {j in N : j != i} x[v,j,i];

# R8: Combustible inicial en depósito (tanque lleno)
subject to InitialFuel {v in V, i in P}:
    f[v,i,i] = F_cap[v] * z[v];

# R9: Solo se recarga en estaciones o depósito
subject to RefuelStations {v in V, i in N diff (E union P)}:
    r[v,i] = 0;

# R10: Límite máximo de recarga según flujo
subject to RefuelLimit {v in V, i in E union P}:
    r[v,i] <= F_cap[v] * sum {j in N : j != i} x[v,j,i];

# ✅ Continuidad en estaciones
subject to StationContinuity {v in V, e in E}:
    sum {i in N : i != e} x[v,i,e] = sum {j in N : j != e} x[v,e,j];

# ✅ Entrada/salida única en depósito (opcional pero recomendado)
subject to DepotSingleExit {v in V}:
    sum {j in N : j != 'PTO01'} x[v,'PTO01',j] <= 1;

subject to DepotSingleEntry {v in V}:
    sum {i in N : i != 'PTO01'} x[v,i,'PTO01'] <= 1;

# ========================
# Restricciones MTZ mejoradas para eliminación de subtours
# ========================

# Inicializar el contador de posición para el depósito
subject to InitPosition {v in V, i in P}:
    u[v,i] = 0;

# Acotar la variable u para nodos no visitados
subject to BoundPosition {v in V, i in N diff P}:
    u[v,i] <= card(N) * sum {j in N: j != i} x[v,j,i];

# Asegurar incremento de posición entre nodos conectados
subject to SubtourElimMTZ {v in V, i in N diff P, j in N diff P: i != j}:
    u[v,i] + 1 <= u[v,j] + card(N) * (1 - x[v,i,j]);