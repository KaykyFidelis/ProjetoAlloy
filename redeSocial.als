// Descrição: Você deve projetar uma especificação simplificada de uma plataforma de mídia social usando 
// o Alloy Analyzer. A plataforma de mídia social deve suportar perfis de usuário, conexões de amizade 
// e publicação de conteúdo de texto. As seguintes restrições devem ser seguidas:

// Um usuário pode ter mais de um perfil. Perfis e usuários podem estar ativos ou inativos.

// Conexões de amizade entre os usuários devem ser estabelecidas. O sistema deve ter um histórico
//  das conexões atuais e apagadas.

// Um usuário pode publicar conteúdo de texto em seu perfil ou nos perfis de seus amigos.

// A especificação Alloy deve representar esses recursos e capturar as relações entre usuários,
// amizades e postagens. Além disso, devem existir restrições para garantir que o modelo seja bem
// definido e satisfaça certas propriedades (por exemplo, os usuários não podem ser amigos de si mesmos, as postagens devem estar associadas a usuários ativos, etc.).

enum Status{
    inativo, ativo
}

enum Publicou{
    TemPublicação, NãoTemPublicação
}

sig Usuario{
    statusUsuario: one Status,
    possui: some Perfil,
    podePublicar: set Perfil,
    amigos: set Usuario,
    exAmigos: set Usuario
}

sig Perfil{
    statusPerfil: one Status,
    publicacoes: one Publicou
}

fact "Restrições do Usuário" {
    all u:Usuario | u not in u.amigos and u not in u.exAmigos
}

fact "Restrições do Perfil" {
    //Caso o usuário ao qual este perfil pertence esteja inativo, o mesmo deve ser inativo também
    all p:Perfil, u:Usuario | (u.statusUsuario = inativo and p in u.possui) implies p.statusPerfil = inativo
    //Cada perfil possui apenas um único usuário que o possui(note que não existem perfis que não pertencem à nenhum usuário)
    all p: Perfil | one u: Usuario | p in u.possui
}

fact "Restrição de Amizade" {
    // Um usuário não pode ser amigo e ex-amigo ao mesmo tempo de outro usuário
    all u1, u2: Usuario | not (u1 in u2.amigos and u1 in u2.exAmigos) and not (u2 in u1.amigos and u2 in u1.exAmigos)
    // A relação de amizade e inimizade deve ser mútua
    all u1, u2: Usuario | (u1 in u2.amigos <=> u2 in u1.amigos) and (u1 in u2.exAmigos <=> u2 in u1.exAmigos)
}

fact "Restrição de Publicação" {
    all u:Usuario | u.podePublicar = u.possui + u.amigos.possui
}

run {} for exactly 3 Usuario, 3 Perfil
