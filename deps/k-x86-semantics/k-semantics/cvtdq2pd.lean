def cvtdq2pd : instruction :=
  definst "cvtdq2pd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_6 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 53 11) 64) (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 53 11) 64));
      setRegister (lhs.of_reg xmm_1) v_6;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_4 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_5 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_3) 53 11) 64) (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 53 11) 64));
      setRegister (lhs.of_reg xmm_1) v_5;
      pure ()
     action
