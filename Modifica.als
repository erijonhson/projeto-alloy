/* 
 Tema 7 em https://docs.google.com/document/d/1aTb65qho0WhN38dV2OWL_4ppcrV-U2u7l6jJVrZxXwY/pub
 TODO:
 [OK] cada Professor ministra duas ou três Disciplinas de 4 horas semanais 
          ~ temos que tratar essa questão de horário? ~ 
 [OK] cada Disciplina possui 4 horas e orientandos possuem 2 ou 4 horas
 [OK] cada Professor pode Orientar Alunos de Graduação  
 [OK] se Professor Doutor, então: 
         [OK] pode orientar Alunos de Mestrado ou Doutorado
         [OK] pode ministrar aulas na pós-graduação, cumulativamente às atividades que já desenvolve 
                (estas disciplinas entram na cota mencionada acima) 
         [OK] Não Doutores não podem ministrar aulas de PosGraduação
 [OK] todos os Professores devem ter 8 atividades de alocação, cada uma de duas ou quatro horas; 
        caso contrário, o professor estará classificado como Atividade Insuficiente. 
         ~ temos que tratar essa questão de horário? ~ 
*/

module AlocacaoProfessoresDSC

--------------------------------------------------------------------------------------
--   ASSINATURAS (Mínimo 5, com ao menos 1 herança - extends ou in)
--------------------------------------------------------------------------------------
abstract sig Docente {
	disciplinas : set Disciplina,
	orientandos : set Orientando 
}

sig AtividadeSuficiente in Docente {}
sig AtividadeInsuficiente in Docente {}

sig Professor extends Docente {}
sig Doutor extends Docente {}

abstract sig Disciplina extends Atividade{}

abstract sig Atividade {	
	horas: some Hora
}
sig DisciplinaDeGraduacao extends Disciplina {}
sig DisciplinaDePosGraduacao extends Disciplina {} -- Apenas professores com titulo de Doutor

abstract sig Hora{}

sig duas, quatro extends Hora{}

abstract sig Orientando extends Atividade{}
sig Graduando extends Orientando {}
sig Mestrando extends Orientando {} -- Apenas professores com titulo de Doutor
sig Doutorando extends Orientando {} -- Apenas professores com titulo de Doutor

--------------------------------------------------------------------------------------
--   FATOS 
--------------------------------------------------------------------------------------

fact DocenteTemDuasOuTresDisciplinas {
	all d : Docente | docentesComDuasOuTresDisciplinas[d]
}

fact DocenteComAtividadesSuficientes {
	all d: Docente | docentePossuiAtividadeSuficiente[d] <=> docenteComAtividadeSuficiente[d]
}

fact DocentesComAtividadesInsuficientes {
	all d: Docente | (docenteTemMenosDeOitoAtividades[d] and docenteTemMenosDe20HorasDeAtividades[d]) <=> docenteComAtividadeInsuficiente[d]
}

fact DisciplinaTemApenasUmDocente{ -- falta assert 
	all d: Disciplina| one d.~disciplinas
}

fact OrientandoTemApenasUmOrientador { 
	all o : Orientando | one o.~orientandos
}

fact ProfessorOrientaApenasGraduando {
	all p : Professor | professorOrientaApenasGraduando[p]
}

fact ProfessorLecionaApenasDisciplinaDeGraduacao {
	all p : Professor | professorLecionaApenasDisciplinaDeGraduacao[p]
}

fact DisciplinaPossuiXHoras {
	all d: Disciplina | disciplinaPossuiXHoras[d]
}

fact OrientandoPossuiXHoras{
	all o: Orientando | orientandoPossuiXHoras[o]
}

--------------------------------------------------------------------------------------
--   PREDICADOS (Mínimo 3) 
--------------------------------------------------------------------------------------

pred docentesComDuasOuTresDisciplinas[d : Docente] {
	#(d.disciplinas) >= 2 and #(d.disciplinas) <= 3
}


pred docentePossuiAtividadeSuficiente[d: Docente]{
	(docenteTemMenosDeOitoAtividades[d] and  docenteTem20HorasDeAtividades[d]) or (docenteTemOitoAtividades[d] and docenteTem20HorasOuMenosDeAtividades[d])
}

pred docentePossuiAtividadeInsuficiente[d: Docente]{
	docenteTemMenosDeOitoAtividades[d] and docenteTemMenosDe20HorasDeAtividades[d]
}
pred docenteTemMenosDeOitoAtividades[d : Docente] {
	#(d.disciplinas + d.orientandos) < 8 
}

pred docenteTemOitoAtividades[d : Docente] {
	#(d.disciplinas + d.orientandos ) = 8 
}

pred docenteTem20HorasDeAtividades[d: Docente]{
	#(d.disciplinas.horas + d.orientandos.horas) = 20 --Como pega essas horas
}

pred docenteTem20HorasOuMenosDeAtividades[d: Docente]{
	#(d.disciplinas.horas + d.orientandos.horas) <= 20 --Como pega essas horas
}

pred docenteTemMenosDe20HorasDeAtividades[d: Docente]{
	#(d.disciplinas.horas + d.orientandos.horas) <  20 --Como pega essas horas
}

pred docenteComAtividadeSuficiente[d : Docente] {
	 d in AtividadeSuficiente
}

pred docenteComAtividadeInsuficiente[d : Docente] {
	 d in AtividadeInsuficiente
}

pred professorOrientaApenasGraduando[p : Professor] {
	#(mestrandosDeDocente[p]) = 0 and #(doutorandosDeDocente[p]) = 0
}

pred professorLecionaApenasDisciplinaDeGraduacao[p : Professor] {
	#(disciplinaDePosGraduacaoDeDocente[p]) = 0
}

pred disciplinaPossuiXHoras[d: Disciplina] {
	#(d.horas) = 4
}

pred orientandoPossuiXHoras[o: Orientando]{
	#(o.horas) = 2 or #(o.horas) = 4
}

--------------------------------------------------------------------------------------
--   FUNÇÕES (Mínimo 3) 
--------------------------------------------------------------------------------------

fun mestrandosDeDocente [d : Docente]  : set Orientando {
	d.orientandos & Mestrando
}

fun doutorandosDeDocente [d : Docente]  : set Orientando {
	d.orientandos & Doutorando
}

fun disciplinaDePosGraduacaoDeDocente [d : Docente] : set Disciplina {
	d.disciplinas & DisciplinaDePosGraduacao
}

--------------------------------------------------------------------------------------
--   ASSERTS  (Mínimo 3 definições e 3 verificações) 
--------------------------------------------------------------------------------------
assert todoDocenteTemDuasOuTresDisciplinas {
    all d : Docente | #(d.disciplinas) >= 2 and #(d.disciplinas) <= 3
}

assert todoProfessorOrientaApenasGraduando {
    all p : Professor | #(mestrandosDeDocente[p]) = 0 and #(doutorandosDeDocente[p]) = 0
}

assert todoProfessorTemApenasDisciplinasDeGraduacao {
    all p : Professor | #(disciplinaDePosGraduacaoDeDocente[p]) = 0
}

assert todoDocenteQueTemMenosQueOitoCadeirasTemAtividadeInsuficiente {
	all d: Docente | #(d.disciplinas + d.orientandos) < 8 => docenteComAtividadeInsuficiente[d]
}

assert todoOrientandoTemApenasUmOrientador {
	all o: Orientando | #(o.~orientandos) = 1
}

assert todoDocenteTemClassificacaoDeAtividadeUnica {
	all d: Docente | (d in AtividadeSuficiente and d !in AtividadeInsuficiente) or (d in AtividadeInsuficiente and d !in AtividadeSuficiente)
}

--------------------------------------------------------------------------------------
--   SHOW 
--------------------------------------------------------------------------------------

pred show[]{}

run show for 8
