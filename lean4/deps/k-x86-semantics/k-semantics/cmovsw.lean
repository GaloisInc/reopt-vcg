def cmovsw1 : instruction :=
  definst "cmovsw" $ do
    pattern fun (v_3268 : reg (bv 16)) (v_3269 : reg (bv 16)) => do
      v_5162 <- getRegister sf;
      v_5164 <- getRegister v_3268;
      v_5165 <- getRegister v_3269;
      setRegister (lhs.of_reg v_3269) (mux (eq v_5162 (expression.bv_nat 1 1)) v_5164 v_5165);
      pure ()
    pat_end;
    pattern fun (v_3261 : Mem) (v_3260 : reg (bv 16)) => do
      v_8618 <- getRegister sf;
      v_8620 <- evaluateAddress v_3261;
      v_8621 <- load v_8620 2;
      v_8622 <- getRegister v_3260;
      setRegister (lhs.of_reg v_3260) (mux (eq v_8618 (expression.bv_nat 1 1)) v_8621 v_8622);
      pure ()
    pat_end
