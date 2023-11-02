/*
A plataforma de mídia social deve suportar perfis de usuário, conexões de amizade e 
publicação de conteúdo de texto. As seguintes restrições devem ser seguidas:

1. Um usuário pode ter mais de um perfil. Perfis e usuários podem estar ativos ou inativos.
2. Conexões de amizade entre os usuários devem ser estabelecidas. 
3. O sistema deve ter um histórico das conexões atuais e apagadas.
4. Um usuário pode publicar conteúdo de texto em seu perfil ou nos perfis de seus amigos.
- A especificação Alloy deve representar esses recursos e capturar as relações entre usuários, amizades e postagens. 

- Além disso, devem existir restrições para garantir que o modelo seja bem definido e satisfaça certas propriedades 
(por exemplo, os usuários não podem ser amigos de si mesmos, as postagens devem 
estar associadas a usuários ativos, etc.).
*/

enum Status{
    inativo,ativo
}

sig Usuario{
    status: Status,
    possui: some Perfil,    // some = 1 ou mais perfis, Usuario nunca terá 0 perfis
    amigos: set Usuario,
    exAmigos: set Usuario
}

sig Perfil{
    status: Status
}

fact "Restrições do Usuário"{
    // Usuario nao pode ser amigo ou ex amigo dele mesmo
    all u:Usuario | u not in u.amigos and u not in u.exAmigos

    // Usuario nao pode ser amigo e ex amigo ao mesmo tempo de outro Usuario
   // all u,x:Usuario | u != x and (u in x.amigos implies u not in x.exAmigos) and (u in x.exAmigos implies u not in x.amigos)
   // all u,x:Usuario | u.amigos, x:
}

fact "Restrições do Perfil"{
    
}

run {} 
