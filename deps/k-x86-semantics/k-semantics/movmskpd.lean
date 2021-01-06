def movmskpd : instruction :=
  definst "movmskpd" $ do
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 64 65);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat (expression.bv_nat 30 0) v_5);
      setRegister (lhs.of_reg r32_1) v_6;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let (v_4 : expression (bv 1)) <- eval (extract v_2 64 65);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat (expression.bv_nat 62 0) v_5);
      setRegister (lhs.of_reg r64_1) v_6;
      pure ()
     action
