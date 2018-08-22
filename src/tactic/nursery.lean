
namespace expr

meta def is_mvar : expr → bool
| (mvar _ _ _) := tt
| _            := ff

end expr
