/* 
 Tema 7 em https://docs.google.com/document/d/1aTb65qho0WhN38dV2OWL_4ppcrV-U2u7l6jJVrZxXwY/pub
 TODO:
 [OK] cada Professor ministra duas ou três Disciplinas de 4 horas semanais 
          ~ temos que tratar essa questão de horário? ~ 
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

sig AtividadeInsuficiente in Docente{}
sig Professor extends Docente {}
sig Doutor extends Docente {}

abstract sig Atividade{}
sig DisciplinaDeGraduacao extends Atividade {}
sig DisciplinaDePosGraduacao extends Atividade {} -- Apenas professores com titulo de doutor
sig AtividadeExtra extends Atividade {} -- Projetos, atividades administrativas, etc

abstract sig Orientando{}
sig Graduando extends Orientando {}
sig Mestrando extends Orientando {} -- Apenas professores com titulo de doutor
sig Doutorando extends Orientando {} -- Apenas professores com titulo de doutor

--------------------------------------------------------------------------------------
--   FATOS 
--------------------------------------------------------------------------------------

fact DocenteTemDuasOuTresDisciplinas {
	all d : Docente | docentesComDuasOuTresDisciplinas[d]
}

fact DocentesComAtividadesInsuficientes{
	all d:Docente | docentesComMaisDeOitoAtividades[d] || docenteComAtividadeInsuficiente[d]
}

fact ProfessorTemDuasOuTresDisciplinas {
	all d : Docente | docentesComDuasOuTresDisciplinas[d]
}

fact DisciplinaTemApenasUmDoutor { -- falta assert 
	all d : Atividade | one d.~disciplinas
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

--------------------------------------------------------------------------------------
--   PREDICADOS (Mínimo 3) 
--------------------------------------------------------------------------------------

pred docenteComAtividadeInsuficiente[d : Docente]{
	 d in AtividadeInsuficiente
}

pred docentesComMaisDeOitoAtividades[d : Docente]{
	#(d.disciplinas + d.orientandos) >=8
}

pred docentesComDuasOuTresDisciplinas[d : Docente] {
	#(disciplinasDeDocente[d]) >= 2 && #(disciplinasDeDocente[d]) <= 3
}


pred professorOrientaApenasGraduando[p : Professor] {
	#(mestrandosDeDocente[p]) = 0 && #(doutorandosDeDocente[p]) = 0
}

pred professorLecionaApenasDisciplinaDeGraduacao[p : Professor] {
	#(disciplinaDePosGraduacaoDeDocente[p]) = 0
}

--------------------------------------------------------------------------------------
--   FUNÇÕES (Mínimo 3) 
--------------------------------------------------------------------------------------

fun disciplinasDeDocente [d : Docente]  : set Atividade {
	d.disciplinas
}

fun mestrandosDeDocente [d : Docente]  : set Orientando {
	d.orientandos & Mestrando
}

fun doutorandosDeDocente [d : Docente]  : set Orientando {
	d.orientandos & Doutorando
}

fun disciplinaDePosGraduacaoDeDocente [d : Docente] : set Atividade {
	d.disciplinas & DisciplinaDePosGraduacao
}

--------------------------------------------------------------------------------------
--   ASSERTS  (Mínimo 3 definições e 3 verificações) 
--------------------------------------------------------------------------------------

assert todoDocenteTemDuasOuTresDisciplinas {
    all d : Docente | #(disciplinasDeDocente[d]) >= 2 && #(disciplinasDeDocente[d]) <= 3
}

-- check todoDocenteTemDuasOuTresDisciplinas for 20

assert todoProfessorOrientaApenasGraduando {
    all p : Professor | #(mestrandosDeDocente[p]) = 0 && #(doutorandosDeDocente[p]) = 0
}

-- check todoProfessorOrientaApenasGraduando for 20

assert todoProfessorTemApenasDisciplinasDeGraduacao {
    all p : Professor | #(disciplinaDePosGraduacaoDeDocente[p]) = 0
}
-- check todoProfessorTemApenasDisciplinasDeGraduacao for 20

assert todoDocenteQueTemMenosQueOitoCadeirasTemAtividadeInsuficiente{
	all d: Docente | #(d.disciplinas + d.orientandos) <8 || docenteComAtividadeInsuficiente[d]
}


assert todoOrientandoTemApenasUmOrientador {
	all o:Orientando | #(o.~orientandos) = 1
}

-- check todoOrientandoTemApenasUmOrientador for 20

--------------------------------------------------------------------------------------
--   SHOW 
--------------------------------------------------------------------------------------

pred show[]{}

run show for 8
