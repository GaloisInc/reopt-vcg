def cmovnlw1 : instruction :=
  definst "cmovnlw" $ do
    pattern fun (v_3067 : reg (bv 16)) (v_3068 : reg (bv 16)) => do
      v_4830 <- getRegister sf;
      v_4831 <- getRegister of;
      v_4833 <- getRegister v_3067;
      v_4834 <- getRegister v_3068;
      setRegister (lhs.of_reg v_3068) (mux (eq v_4830 v_4831) v_4833 v_4834);
      pure ()
    pat_end;
    pattern fun (v_3063 : Mem) (v_3064 : reg (bv 16)) => do
      v_8139 <- getRegister sf;
      v_8140 <- getRegister of;
      v_8142 <- evaluateAddress v_3063;
      v_8143 <- load v_8142 2;
      v_8144 <- getRegister v_3064;
      setRegister (lhs.of_reg v_3064) (mux (eq v_8139 v_8140) v_8143 v_8144);
      pure ()
    pat_end
