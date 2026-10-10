(** The five-element Heyting algebra used independently of the refutation. *)
Inductive H5 : Type := HBot | H1 | H2 | H12 | HTop.

Definition H5_le (x y : H5) : Prop :=
  match x, y with
  | HBot, _ => True
  | _, HTop => True
  | H1, H1 | H1, H12 => True
  | H2, H2 | H2, H12 => True
  | H12, H12 => True
  | _, _ => False
  end.

Lemma H5_le_refl : forall x, H5_le x x. Proof. destruct x; exact I. Defined.
Lemma H5_le_trans : forall x y z, H5_le y z -> H5_le x y -> H5_le x z.
Proof. destruct x, y, z; simpl; tauto. Defined.

Definition H5_meet (x y : H5) : H5 :=
  match x, y with
  | HBot, _ | _, HBot => HBot
  | HTop, a | a, HTop => a
  | H1, H1 | H1, H12 | H12, H1 => H1
  | H2, H2 | H2, H12 | H12, H2 => H2
  | H12, H12 => H12
  | H1, H2 | H2, H1 => HBot
  end.

Definition H5_join (x y : H5) : H5 :=
  match x, y with
  | HTop, _ | _, HTop => HTop
  | HBot, a | a, HBot => a
  | H12, _ | _, H12 => H12
  | H1, H1 => H1
  | H2, H2 => H2
  | H1, H2 | H2, H1 => H12
  end.

Definition H5_impl (x y : H5) : H5 :=
  match x, y with
  | HBot, _ | _, HTop => HTop
  | HTop, a => a
  | H12, H1 => H1
  | H12, H2 => H2
  | H12, HBot => HBot
  | H1, H1 | H1, H12 => HTop
  | H1, H2 | H1, HBot => H2
  | H2, H2 | H2, H12 => HTop
  | H2, H1 | H2, HBot => H1
  | H12, H12 => HTop
  end.
