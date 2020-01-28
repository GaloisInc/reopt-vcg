def haddpd : instruction :=
  definst "haddpd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 0 64));
      v_6 <- getRegister (lhs.of_reg xmm_1);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_6 64 128));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_6 0 64));
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_add v_4 v_5) 64) (fp_bitcast_to_bv (fp_add v_7 v_8) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      v_3 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_2 64 128));
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_2 0 64));
      v_5 <- getRegister (lhs.of_reg xmm_1);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 64 128));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 0 64));
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_add v_3 v_4) 64) (fp_bitcast_to_bv (fp_add v_6 v_7) 64));
      pure ()
    pat_end
