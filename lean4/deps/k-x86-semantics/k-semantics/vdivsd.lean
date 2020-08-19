def vdivsd : instruction :=
  definst "vdivsd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 v_5);
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 8;
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (fp_bitcast_to_bv (fp_div v_6 v_9) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 v_5);
      v_7 <- getRegister (lhs.of_reg xmm_0);
      (v_8 : expression (bv 64)) <- eval (extract v_7 64 128);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (fp_bitcast_to_bv (fp_div v_6 v_9) 64));
      pure ()
    pat_end