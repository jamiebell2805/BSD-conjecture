import tactic
import topology.instances.real
import order.filter.at_top_bot

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
noncomputable theory
open finset filter function classical
open_locale topological_space classical big_operators nnreal

variables [comm_monoid α] [topological_space α]

def has_prod (f : β → α) (a : α) : Prop := 
tendsto (λs:finset β, ∏ b in s, f b) at_top (𝓝 a)

def prodable (f : β → α) : Prop := ∃a, has_prod f a

@[irreducible] def tprod {β} (f : β → α) := 
if h : prodable f then classical.some h else 1
