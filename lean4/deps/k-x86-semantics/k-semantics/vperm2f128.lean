def vperm2f1281 : instruction :=
  definst "vperm2f128" $ do
    pattern fun (v_2949 : imm int) (v_2951 : reg (bv 256)) (v_2952 : reg (bv 256)) (v_2953 : reg (bv 256)) => do
      v_8135 <- eval (handleImmediateWithSignExtend v_2949 8 8);
      v_8138 <- eval (extract v_8135 2 4);
      v_8140 <- getRegister v_2952;
      v_8141 <- eval (extract v_8140 128 256);
      v_8143 <- eval (extract v_8140 0 128);
      v_8145 <- getRegister v_2951;
      v_8146 <- eval (extract v_8145 128 256);
      v_8147 <- eval (extract v_8145 0 128);
      v_8154 <- eval (extract v_8135 6 8);
      setRegister (lhs.of_reg v_2953) (concat (mux (eq (extract v_8135 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_8138 (expression.bv_nat 2 0)) v_8141 (mux (eq v_8138 (expression.bv_nat 2 1)) v_8143 (mux (eq v_8138 (expression.bv_nat 2 2)) v_8146 v_8147)))) (mux (eq (extract v_8135 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_8154 (expression.bv_nat 2 0)) v_8141 (mux (eq v_8154 (expression.bv_nat 2 1)) v_8143 (mux (eq v_8154 (expression.bv_nat 2 2)) v_8146 v_8147)))));
      pure ()
    pat_end;
    pattern fun (v_2944 : imm int) (v_2943 : Mem) (v_2945 : reg (bv 256)) (v_2946 : reg (bv 256)) => do
      v_16934 <- eval (handleImmediateWithSignExtend v_2944 8 8);
      v_16937 <- eval (extract v_16934 2 4);
      v_16939 <- getRegister v_2945;
      v_16940 <- eval (extract v_16939 128 256);
      v_16942 <- eval (extract v_16939 0 128);
      v_16944 <- evaluateAddress v_2943;
      v_16945 <- load v_16944 32;
      v_16946 <- eval (extract v_16945 128 256);
      v_16947 <- eval (extract v_16945 0 128);
      v_16954 <- eval (extract v_16934 6 8);
      setRegister (lhs.of_reg v_2946) (concat (mux (eq (extract v_16934 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_16937 (expression.bv_nat 2 0)) v_16940 (mux (eq v_16937 (expression.bv_nat 2 1)) v_16942 (mux (eq v_16937 (expression.bv_nat 2 2)) v_16946 v_16947)))) (mux (eq (extract v_16934 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 128 0) (mux (eq v_16954 (expression.bv_nat 2 0)) v_16940 (mux (eq v_16954 (expression.bv_nat 2 1)) v_16942 (mux (eq v_16954 (expression.bv_nat 2 2)) v_16946 v_16947)))));
      pure ()
    pat_end
