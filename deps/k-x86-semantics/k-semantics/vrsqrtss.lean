def vrsqrtss : instruction :=
  definst "vrsqrtss" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 4;
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_6));
      let v_8 <- eval (concat v_4 (fp_bitcast_to_bv (fp_div 1e+00 v_7) 32));
      setRegister (lhs.of_reg xmm_2) v_8;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_6));
      let v_8 <- eval (concat v_4 (fp_bitcast_to_bv (fp_div 1e+00 v_7) 32));
      setRegister (lhs.of_reg xmm_2) v_8;
      pure ()
     action
