// ============================================================
// Simulador de rentabilidad - Laboratorio 2 (Modelos y Simulación)
// Generador: congruencial mixto  X(i+1) = (a * X(i) + c) mod m
//            U(i) = X(i+1) / m, en el intervalo [0, 1)
// ============================================================

var USOS_POR_CORRIDA = 4;   // números uniformes que consume cada corrida (2 + 1 + 1)
var FILAS_TABLA = 12;       // cuántas corridas se muestran en la tabla
var MAX_CORRIDAS = 100000;
var Z95 = 1.96;             // para el intervalo de confianza del 95 %


// ------------------------------------------------------------
// 1. VALIDACIÓN DE DATOS
// ------------------------------------------------------------
function esEntero(x) {
    return typeof x === "number" && isFinite(x) && Math.floor(x) === x;
}

// Devuelve { errores: [...], avisos: [...] }
function validarEntradas(d) {
    var errores = [];
    var avisos = [];
    var campos = ["semilla", "a", "c", "m", "corridas", "probMinima", "mediaClientes",
                  "desvioClientes", "costoFijo", "ticketMin", "ticketModa", "ticketMax",
                  "costoMin", "costoMax"];

    for (var i = 0; i < campos.length; i++) {
        var v = d[campos[i]];
        if (typeof v !== "number" || isNaN(v)) {
            errores.push("El campo '" + campos[i] + "' está vacío o no es un número.");
        }
    }
    if (errores.length > 0) {
        return { errores: errores, avisos: avisos };
    }

    // Generador
    if (!esEntero(d.semilla) || !esEntero(d.a) || !esEntero(d.c) || !esEntero(d.m)) {
        errores.push("X₀, a, c y m deben ser números enteros.");
    } else {
        if (d.semilla <= 0) errores.push("La semilla X₀ debe ser mayor que 0.");
        if (d.a <= 0) errores.push("El multiplicador a debe ser mayor que 0.");
        if (d.c <= 0) errores.push("El incremento c debe ser mayor que 0.");
        if (d.m <= d.semilla) errores.push("El módulo m debe ser mayor que la semilla X₀.");
        if (d.m <= d.a) errores.push("El módulo m debe ser mayor que a.");
        if (d.a * (d.m - 1) + d.c > Number.MAX_SAFE_INTEGER) {
            errores.push("a, c y m son demasiado grandes: JavaScript perdería precisión al calcular a·X + c.");
        }
    }

    // Corridas
    if (!esEntero(d.corridas) || d.corridas < 1) {
        errores.push("La cantidad de corridas debe ser un entero mayor o igual a 1.");
    } else if (d.corridas > MAX_CORRIDAS) {
        errores.push("La cantidad de corridas no puede superar " + MAX_CORRIDAS + ".");
    }

    // Criterio
    if (d.probMinima <= 0 || d.probMinima >= 100) {
        errores.push("La probabilidad mínima exigida debe estar entre 0 y 100 (sin incluirlos).");
    }

    // Clientes: Normal
    if (d.mediaClientes <= 0) errores.push("La media de clientes μ debe ser mayor que 0.");
    if (d.desvioClientes <= 0) errores.push("El desvío de clientes σ debe ser mayor que 0.");
    if (d.mediaClientes > 0 && d.desvioClientes > 0 && d.mediaClientes < 3 * d.desvioClientes) {
        errores.push("Se exige μ ≥ 3σ para que la Normal casi no genere clientes negativos.");
    }

    // Ticket: Triangular
    if (d.ticketMin < 0) errores.push("El ticket mínimo no puede ser negativo.");
    if (d.ticketMin >= d.ticketMax) errores.push("El ticket mínimo debe ser menor que el máximo.");
    if (d.ticketModa < d.ticketMin || d.ticketModa > d.ticketMax) {
        errores.push("El ticket más probable debe estar entre el mínimo y el máximo.");
    }

    // Costo: Uniforme
    if (d.costoMin < 0) errores.push("El costo variable mínimo no puede ser negativo.");
    if (d.costoMin >= d.costoMax) errores.push("El costo variable mínimo debe ser menor que el máximo.");

    // Costos fijos
    if (d.costoFijo < 0) errores.push("Los costos fijos no pueden ser negativos.");

    // Aviso de coherencia económica (no bloquea)
    if (errores.length === 0 && d.costoMax >= d.ticketMin) {
        avisos.push("El costo variable máximo ($" + d.costoMax + ") alcanza o supera el ticket mínimo ($" +
                    d.ticketMin + "): algunas corridas pueden tener margen negativo por cliente.");
    }

    return { errores: errores, avisos: avisos };
}


// ------------------------------------------------------------
// 2. GENERADOR CONGRUENCIAL MIXTO
// ------------------------------------------------------------
// Genera hasta 'cantidad' números U en [0,1). Se detiene antes si un valor
// de X se repite (se terminó el período), para no reutilizar números.
function generarUniformes(semilla, a, c, m, cantidad) {
    var us = [];
    var x = semilla;
    var vistos = new Set();
    vistos.add(semilla);
    var cicloCerrado = false;

    while (us.length < cantidad) {
        x = (a * x + c) % m;
        if (vistos.has(x)) {
            cicloCerrado = true;
            break;
        }
        vistos.add(x);
        us.push(x / m);
    }

    return { us: us, cicloCerrado: cicloCerrado };
}


// ------------------------------------------------------------
// 3. TRANSFORMACIÓN DE UNIFORMES EN VARIABLES ALEATORIAS
// ------------------------------------------------------------

// Normal estándar por Box-Muller. Se usa (1 - u1) dentro del logaritmo:
// como u1 está en [0,1), (1 - u1) está en (0,1] y nunca se calcula ln(0).
function normalEstandar(u1, u2) {
    return Math.sqrt(-2 * Math.log(1 - u1)) * Math.cos(2 * Math.PI * u2);
}

// N: clientes del mes (Normal redondeada, nunca negativa)
function generarClientes(mu, sigma, u1, u2) {
    var n = Math.round(mu + sigma * normalEstandar(u1, u2));
    return Math.max(0, n);
}

// P: ticket promedio (Triangular, método de la transformada inversa)
function generarTicket(minimo, moda, maximo, u) {
    var fc = (moda - minimo) / (maximo - minimo);
    if (u < fc) {
        return minimo + Math.sqrt(u * (maximo - minimo) * (moda - minimo));
    }
    return maximo - Math.sqrt((1 - u) * (maximo - minimo) * (maximo - moda));
}

// C: costo variable por cliente (Uniforme entre a y b)
function generarCosto(minimo, maximo, u) {
    return minimo + (maximo - minimo) * u;
}


// ------------------------------------------------------------
// 4. SIMULACIÓN
// ------------------------------------------------------------
function simular(d) {
    var pedidas = d.corridas;
    var gen = generarUniformes(d.semilla, d.a, d.c, d.m, pedidas * USOS_POR_CORRIDA);
    var us = gen.us;
    var posibles = Math.floor(us.length / USOS_POR_CORRIDA);

    var corridas = [];
    var rentables = 0;
    var suma = 0;
    var minimo = Infinity;
    var maximo = -Infinity;

    for (var k = 0; k < posibles; k++) {
        var u1 = us[k * 4];
        var u2 = us[k * 4 + 1];
        var u3 = us[k * 4 + 2];
        var u4 = us[k * 4 + 3];

        var clientes = generarClientes(d.mediaClientes, d.desvioClientes, u1, u2);
        var ticket = generarTicket(d.ticketMin, d.ticketModa, d.ticketMax, u3);
        var costo = generarCosto(d.costoMin, d.costoMax, u4);

        var ingresos = clientes * ticket;
        var costos = clientes * costo + d.costoFijo;
        var ganancia = ingresos - costos;
        var rentable = ganancia > 0;

        if (rentable) rentables++;
        suma += ganancia;
        if (ganancia < minimo) minimo = ganancia;
        if (ganancia > maximo) maximo = ganancia;

        corridas.push({
            numero: k + 1, u1: u1, u2: u2, u3: u3, u4: u4,
            clientes: clientes, ticket: ticket, costo: costo,
            ingresos: ingresos, costos: costos, ganancia: ganancia, rentable: rentable
        });
    }

    var resumen = calcularResumen(d, corridas.length, rentables, suma, minimo, maximo);
    resumen.pedidas = pedidas;
    resumen.numerosUsados = us.length;
    resumen.cicloCerrado = gen.cicloCerrado;

    return { corridas: corridas, resumen: resumen };
}


// ------------------------------------------------------------
// 5. INDICADORES Y EVALUACIÓN DE LA HIPÓTESIS
// ------------------------------------------------------------
// Intervalo de confianza del 95 % para una proporción (método de Wilson).
function intervaloProporcion(p, n) {
    var z2 = Z95 * Z95;
    var centro = (p + z2 / (2 * n)) / (1 + z2 / n);
    var mitad = Z95 * Math.sqrt(p * (1 - p) / n + z2 / (4 * n * n)) / (1 + z2 / n);
    return { inferior: centro - mitad, superior: centro + mitad };
}

function calcularResumen(d, n, rentables, suma, minimo, maximo) {
    var umbral = d.probMinima / 100;
    var r = {
        n: n,
        rentables: rentables,
        noRentables: n - rentables,
        umbral: umbral
    };
    if (n === 0) {
        r.decision = "sin datos";
        return r;
    }

    r.pHat = rentables / n;
    r.promedio = suma / n;
    r.minimo = minimo;
    r.maximo = maximo;

    var ic = intervaloProporcion(r.pHat, n);
    r.icInferior = ic.inferior;
    r.icSuperior = ic.superior;

    if (ic.inferior > umbral) {
        r.decision = "aceptada";
    } else if (ic.superior < umbral) {
        r.decision = "rechazada";
    } else {
        r.decision = "no concluyente";
    }
    return r;
}


// ------------------------------------------------------------
// 6. PANTALLA (solo se ejecuta en el navegador)
// ------------------------------------------------------------
function numero(id) {
    var texto = document.getElementById(id).value.trim();
    if (texto === "") return NaN;
    return Number(texto);
}

function leerEntradas() {
    return {
        semilla: numero("semilla"),
        a: numero("a"),
        c: numero("c"),
        m: numero("m"),
        corridas: numero("corridas"),
        probMinima: numero("probMinima"),
        mediaClientes: numero("mediaClientes"),
        desvioClientes: numero("desvioClientes"),
        costoFijo: numero("costoFijo"),
        ticketMin: numero("ticketMin"),
        ticketModa: numero("ticketModa"),
        ticketMax: numero("ticketMax"),
        costoMin: numero("costoMin"),
        costoMax: numero("costoMax")
    };
}

function pesos(x) {
    return "$" + x.toLocaleString("es-AR", { maximumFractionDigits: 0 });
}

function porcentaje(x) {
    return (x * 100).toFixed(2) + " %";
}

function mostrarLista(idCaja, mensajes) {
    var caja = document.getElementById(idCaja);
    if (mensajes.length === 0) {
        caja.classList.add("oculto");
        caja.innerHTML = "";
        return;
    }
    var html = "<ul>";
    for (var i = 0; i < mensajes.length; i++) {
        html += "<li>" + mensajes[i] + "</li>";
    }
    caja.innerHTML = html + "</ul>";
    caja.classList.remove("oculto");
}

function dibujarResumen(r) {
    var datos = [
        ["Corridas pedidas", r.pedidas],
        ["Corridas simuladas", r.n],
        ["Números U utilizados", r.numerosUsados],
        ["Período del generador", r.cicloCerrado ? "Se cerró el ciclo (se cortó ahí)" : "No se repitió ningún valor"],
        ["Ganancia promedio", pesos(r.promedio)],
        ["Ganancia máxima", pesos(r.maximo)],
        ["Ganancia mínima (o mayor pérdida)", pesos(r.minimo)],
        ["Corridas rentables", r.rentables],
        ["Corridas no rentables", r.noRentables],
        ["Probabilidad estimada de ganancia", porcentaje(r.pHat)],
        ["Intervalo de confianza 95 %", porcentaje(r.icInferior) + " a " + porcentaje(r.icSuperior)]
    ];
    var html = "";
    for (var i = 0; i < datos.length; i++) {
        html += '<div class="dato"><span>' + datos[i][0] + "</span><strong>" + datos[i][1] + "</strong></div>";
    }
    document.getElementById("resumen").innerHTML = html;
}

function dibujarDecision(r) {
    var caja = document.getElementById("decision");
    var texto = "Hipótesis: P(ganancia mensual > 0) > " + (r.umbral * 100) + " %. ";

    if (r.decision === "aceptada") {
        caja.className = "caja acepta";
        texto += "<strong>HIPÓTESIS ACEPTADA.</strong> Todo el intervalo de confianza queda por encima de " +
                 (r.umbral * 100) + " %: conviene abrir la sucursal bajo estos supuestos.";
    } else if (r.decision === "rechazada") {
        caja.className = "caja rechaza";
        texto += "<strong>HIPÓTESIS RECHAZADA.</strong> Todo el intervalo de confianza queda por debajo de " +
                 (r.umbral * 100) + " %: no conviene abrir la sucursal bajo estos supuestos.";
    } else {
        caja.className = "caja neutro";
        texto += "<strong>NO CONCLUYENTE.</strong> El umbral de " + (r.umbral * 100) +
                 " % cae dentro del intervalo de confianza: hacen falta más corridas (o un generador con período más largo).";
    }
    caja.innerHTML = texto;
}

function dibujarTabla(corridas) {
    var cuerpo = document.getElementById("cuerpoTabla");
    var html = "";
    var limite = Math.min(FILAS_TABLA, corridas.length);

    for (var i = 0; i < limite; i++) {
        var f = corridas[i];
        html += "<tr>" +
            "<td>" + f.numero + "</td>" +
            "<td>" + f.u1.toFixed(6) + "</td>" +
            "<td>" + f.u2.toFixed(6) + "</td>" +
            "<td>" + f.u3.toFixed(6) + "</td>" +
            "<td>" + f.u4.toFixed(6) + "</td>" +
            "<td>" + f.clientes + "</td>" +
            "<td>" + pesos(f.ticket) + "</td>" +
            "<td>" + pesos(f.costo) + "</td>" +
            "<td>" + pesos(f.ingresos) + "</td>" +
            "<td>" + pesos(f.costos) + "</td>" +
            '<td class="' + (f.rentable ? "ganancia" : "perdida") + '">' + pesos(f.ganancia) + "</td>" +
            "<td>" + (f.rentable ? "Rentable" : "No rentable") + "</td>" +
            "</tr>";
    }
    cuerpo.innerHTML = html;
    document.getElementById("notaTabla").textContent =
        "Se muestran las primeras " + limite + " de " + corridas.length +
        " corridas. El resumen de arriba usa todas las corridas.";
}

function ejecutar(evento) {
    evento.preventDefault();

    var datos = leerEntradas();
    var validacion = validarEntradas(datos);
    mostrarLista("errores", validacion.errores);
    mostrarLista("avisos", validacion.avisos);

    var resultados = document.getElementById("resultados");
    if (validacion.errores.length > 0) {
        resultados.classList.add("oculto");
        return;
    }

    var salida = simular(datos);

    if (salida.resumen.n === 0) {
        mostrarLista("errores", ["El período del generador es demasiado corto: no alcanza para una corrida completa (se necesitan " +
        USOS_POR_CORRIDA + " números distintos). Probá con otros a, c, m o semilla."]);
        resultados.classList.add("oculto");
        return;
    }

    var avisos = validacion.avisos.slice();
    if (salida.resumen.n < salida.resumen.pedidas) {
        avisos.push("Se pidieron " + salida.resumen.pedidas + " corridas, pero el período del generador solo alcanza para " +
                    salida.resumen.n + ". Se simuló hasta ahí para no repetir números.");
    }
    if (salida.resumen.n < 30) {
        avisos.push("Hay muy pocas corridas (" + salida.resumen.n + "): la estimación de la probabilidad es poco confiable.");
    }
    mostrarLista("avisos", avisos);

    dibujarResumen(salida.resumen);
    dibujarDecision(salida.resumen);
    dibujarTabla(salida.corridas);
    resultados.classList.remove("oculto");
}

if (typeof document !== "undefined") {
    document.getElementById("formulario").addEventListener("submit", ejecutar);
}

// Solo para poder probar las funciones fuera del navegador (no afecta al simulador)
if (typeof module !== "undefined") {
    module.exports = {
        validarEntradas: validarEntradas,
        generarUniformes: generarUniformes,
        normalEstandar: normalEstandar,
        generarClientes: generarClientes,
        generarTicket: generarTicket,
        generarCosto: generarCosto,
        simular: simular
    };
}