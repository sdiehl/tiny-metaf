type Id = lam (a : *). a;
let id : forall a. a -> a = /\a. \(x : a). x;
eval id [Id] 0;
