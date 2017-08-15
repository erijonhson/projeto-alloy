/* 
 Tema 7 em https://docs.google.com/document/d/1aTb65qho0WhN38dV2OWL_4ppcrV-U2u7l6jJVrZxXwY/pub
 TODO:
 [OK] cada Professor ministra duas ou três Disciplinas de 4 horas semanais 
 [OK] cada Professor pode Orientar Alunos de Graduação  
 [OK] se Professor Doutor, então: 
         [OK] pode orientar Alunos de Mestrado ou Doutorado
         [OK] pode ministrar aulas na pós-graduação, cumulativamente às atividades que já desenvolve 
                (estas disciplinas entram na cota mencionada acima) 
         [OK] Não Doutores não podem ministrar aulas de PosGraduação
 [OK] todos os Professores devem ter 8 atividades de alocação, cada uma de duas ou quatro horas; 
        caso contrário, o professor estará classificado como Atividade Insuficiente. 
 [OK] Dois Docentes podem dividir a mesma Disciplina 
 [OK] Horas como classificação de atividades.
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

abstract sig Disciplina {}
sig DisciplinaDeGraduacao extends Disciplina {}
sig DisciplinaDePosGraduacao extends Disciplina {} -- Apenas professores com titulo de Doutor

sig DisciplinaDeQuatroHoras in Disciplina {}

abstract sig Orientando {}
sig Graduando extends Orientando {}
sig Mestrando extends Orientando {} -- Apenas professores com titulo de Doutor
sig Doutorando extends Orientando {} -- Apenas professores com titulo de Doutor

sig OrientacaoDeDuasHoras, OrientacaoDeQuatroHoras in Orientando {}

sig AtividadeExtra{}
sig AtividadeExtraDeDuasHoras, AtividadeExtraDeQuatroHoras in AtividadeExtra {}

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

fact DisciplinaTemUmOuDoisDocente {
	all d : Disciplina | disciplinaTemUmOuDoisDocentes[d]
}

fact DisciplinaTemQuatroHoras {
	all d : Disciplina | d in DisciplinaDeQuatroHoras
}

fact OrientandoTemApenasUmOrientador {
	all o : Orientando | one o.~orientandos
}

fact AtividadeExtraTemPeloMenosUmDocente {
	all a: AtividadeExtra | some a.~atividadesExtras
}

fact DuasOuQuatroHoras {
	(all a: AtividadeExtra | (a in AtividadeExtraDeDuasHoras and a !in AtividadeExtraDeQuatroHoras) or 
										 (a in AtividadeExtraDeQuatroHoras and a !in AtividadeExtraDeDuasHoras)) and
	(all o: Orientando | (o in OrientacaoDeDuasHoras and o !in OrientacaoDeQuatroHoras) or 
									(o in OrientacaoDeQuatroHoras and o !in OrientacaoDeDuasHoras))
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
	todasAtividades[d] >= 8
}

pred docenteComAtividadeSuficiente[d : Docente] {
	 d in AtividadeSuficiente
}

pred docenteTemMenosDeOitoAtividades[d : Docente] {
	todasAtividades[d] < 8
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

pred disciplinaTemUmOuDoisDocentes[d: Disciplina] {
	#(d.~disciplinas) = 1 or #(d.~disciplinas) = 2
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

fun todasAtividades[d : Docente] : Int {
	#(d.disciplinas + d.orientandos + d.atividadesExtras)
}

--------------------------------------------------------------------------------------
--   ASSERTS  (Mínimo 3 definições e 3 verificações) 
--------------------------------------------------------------------------------------

assert todoDocenteTemDuasOuTresDisciplinas {
    all d : Docente | #(d.disciplinas) >= 2 and #(d.disciplinas) <= 3
}

check todoDocenteTemDuasOuTresDisciplinas for 20

assert todoProfessorOrientaApenasGraduando {
    all p : Professor | #(mestrandosDeDocente[p]) = 0 and #(doutorandosDeDocente[p]) = 0
}

check todoProfessorOrientaApenasGraduando for 20

assert todoProfessorTemApenasDisciplinasDeGraduacao {
    all p : Professor | #(disciplinaDePosGraduacaoDeDocente[p]) = 0
}

check todoProfessorTemApenasDisciplinasDeGraduacao for 20

assert todoDocenteQueTemMenosQueOitoCadeirasTemAtividadeInsuficiente {
	all d: Docente | (todasAtividades[d] < 8) => docenteComAtividadeInsuficiente[d]
}

check todoDocenteQueTemMenosQueOitoCadeirasTemAtividadeInsuficiente for 20

assert todoOrientandoTemApenasUmOrientador {
	all o: Orientando | #(o.~orientandos) = 1
}

check todoOrientandoTemApenasUmOrientador for 20

assert todoDocenteTemClassificacaoDeAtividadeUnica {
	all d: Docente | (d in AtividadeSuficiente and d !in AtividadeInsuficiente) or (d in AtividadeInsuficiente and d !in AtividadeSuficiente)
}

check todoDocenteTemClassificacaoDeAtividadeUnica for 20

assert todaDisciplinaTemUmOuDoisDocentes {
	all d: Disciplina | #(d.~disciplinas) = 1 or #(d.~disciplinas) = 2
}

check todaDisciplinaTemUmOuDoisDocentes for 20

--------------------------------------------------------------------------------------
--   SHOW 
--------------------------------------------------------------------------------------

pred show[]{#Docente > 3}

run show for 8
