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
 [] Dois Docentes podem dividir a mesma disciplinas 
 [] Horas como classificação de atividades. 
*/

module AlocacaoProfessoresDSC

--------------------------------------------------------------------------------------
--   ASSINATURAS (Mínimo 5, com ao menos 1 herança - extends ou in)
--------------------------------------------------------------------------------------
abstract sig Docente {
	disciplinas : set Disciplina,
	orientandos : set Orientando,
	atividadesExtras: set AtividadeExtra
	
}

sig AtividadeSuficiente in Docente {}
sig AtividadeInsuficiente in Docente {}

sig Professor extends Docente {}
sig Doutor extends Docente {}

abstract sig Atividade{}

abstract sig Disciplina extends Atividade{}

sig AtividadeExtra extends Atividade {}

sig DisciplinaDeGraduacao extends Disciplina {}
sig DisciplinaDePosGraduacao extends Disciplina {} -- Apenas professores com titulo de Doutor

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
	all d: Docente | docenteTemOitoOuMaisAtividades[d] <=> docenteComAtividadeSuficiente[d]
}

fact DocentesComAtividadesInsuficientes {
	all d: Docente | docenteTemMenosDeOitoAtividades[d] <=> docenteComAtividadeInsuficiente[d]
}

fact DisciplinaTemUmOuDoisDocente { -- falta assert 
	all d : Disciplina | disciplinaTemUmOuDoisDocente[d]
}

fact OrientandoTemApenasUmOrientador { 
	all o : Orientando | one o.~orientandos
}

fact AtividadeExtraTemPeloMenosUmDocente {
	all a: AtividadeExtra | some a.~atividadesExtras
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

pred docentesComDuasOuTresDisciplinas[d : Docente] {
	#(d.disciplinas) >= 2 and #(d.disciplinas) <= 3
}

pred docenteTemOitoOuMaisAtividades[d : Docente] {
	totalDeAtividades[d] >= 8
}

pred disciplinaTemUmOuDoisDocente[d: Disciplina] {
	#(d.~disciplinas) = 1 or #(d.~disciplinas) = 2
}

pred docenteComAtividadeSuficiente[d : Docente] {
	 d in AtividadeSuficiente
}

pred docenteTemMenosDeOitoAtividades[d : Docente] {
	totalDeAtividades[d] < 8
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

fun totalDeAtividades[d: Docente] : Int{
	#(d.disciplinas + d.orientandos + d.atividadesExtras)
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
	all d: Docente | totalDeAtividades[d] < 8 => docenteComAtividadeInsuficiente[d]
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

pred show[]{ #Docente > 3}

run show for 8
