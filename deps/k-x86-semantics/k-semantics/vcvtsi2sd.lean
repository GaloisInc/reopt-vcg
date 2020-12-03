def vcvtsi2sd : instruction :=
  definst "vcvtsi2sd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 4;
      let v_7 <- eval (concat v_4 (fp_bitcast_to_bv (Int2Float (svalueMInt v_6) 53 11) 64));
      setRegister (lhs.of_reg xmm_2) v_7;
      pure ()
     action
