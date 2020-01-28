def addps : instruction :=
  definst "addps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 0 32));
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 0 32));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 32 64));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 32 64));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 64 96));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 64 96));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 96 128));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 96 128));
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_add v_3 v_6) 32) (concat (fp_bitcast_to_bv (fp_add v_7 v_8) 32) (concat (fp_bitcast_to_bv (fp_add v_9 v_10) 32) (fp_bitcast_to_bv (fp_add v_11 v_12) 32))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 0 32));
      v_4 <- getRegister (lhs.of_reg xmm_0);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 0 32));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 32 64));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 32 64));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 64 96));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 64 96));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 96 128));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 96 128));
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_add v_3 v_5) 32) (concat (fp_bitcast_to_bv (fp_add v_6 v_7) 32) (concat (fp_bitcast_to_bv (fp_add v_8 v_9) 32) (fp_bitcast_to_bv (fp_add v_10 v_11) 32))));
      pure ()
    pat_end
