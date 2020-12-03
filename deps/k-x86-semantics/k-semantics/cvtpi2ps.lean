def cvtpi2ps : instruction :=
  definst "cvtpi2ps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 8;
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract v_5 32 64);
      let v_8 <- eval (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_6) 24 8) 32) (fp_bitcast_to_bv (Int2Float (svalueMInt v_7) 24 8) 32));
      let v_9 <- eval (concat v_3 v_8);
      setRegister (lhs.of_reg xmm_1) v_9;
      pure ()
     action
