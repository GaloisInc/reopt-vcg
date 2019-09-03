def vpabsd1 : instruction :=
  definst "vpabsd" $ do
    pattern fun (v_3197 : reg (bv 128)) (v_3198 : reg (bv 128)) => do
      v_5711 <- getRegister v_3197;
      v_5712 <- eval (extract v_5711 0 32);
      v_5719 <- eval (extract v_5711 32 64);
      v_5726 <- eval (extract v_5711 64 96);
      v_5733 <- eval (extract v_5711 96 128);
      setRegister (lhs.of_reg v_3198) (concat (mux (ugt v_5712 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5712 (mi (bitwidthMInt v_5712) -1))) v_5712) (concat (mux (ugt v_5719 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5719 (mi (bitwidthMInt v_5719) -1))) v_5719) (concat (mux (ugt v_5726 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5726 (mi (bitwidthMInt v_5726) -1))) v_5726) (mux (ugt v_5733 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5733 (mi (bitwidthMInt v_5733) -1))) v_5733))));
      pure ()
    pat_end;
    pattern fun (v_3206 : reg (bv 256)) (v_3207 : reg (bv 256)) => do
      v_5748 <- getRegister v_3206;
      v_5749 <- eval (extract v_5748 0 32);
      v_5756 <- eval (extract v_5748 32 64);
      v_5763 <- eval (extract v_5748 64 96);
      v_5770 <- eval (extract v_5748 96 128);
      v_5777 <- eval (extract v_5748 128 160);
      v_5784 <- eval (extract v_5748 160 192);
      v_5791 <- eval (extract v_5748 192 224);
      v_5798 <- eval (extract v_5748 224 256);
      setRegister (lhs.of_reg v_3207) (concat (mux (ugt v_5749 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5749 (mi (bitwidthMInt v_5749) -1))) v_5749) (concat (mux (ugt v_5756 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5756 (mi (bitwidthMInt v_5756) -1))) v_5756) (concat (mux (ugt v_5763 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5763 (mi (bitwidthMInt v_5763) -1))) v_5763) (concat (mux (ugt v_5770 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5770 (mi (bitwidthMInt v_5770) -1))) v_5770) (concat (mux (ugt v_5777 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5777 (mi (bitwidthMInt v_5777) -1))) v_5777) (concat (mux (ugt v_5784 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5784 (mi (bitwidthMInt v_5784) -1))) v_5784) (concat (mux (ugt v_5791 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5791 (mi (bitwidthMInt v_5791) -1))) v_5791) (mux (ugt v_5798 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5798 (mi (bitwidthMInt v_5798) -1))) v_5798))))))));
      pure ()
    pat_end;
    pattern fun (v_3192 : Mem) (v_3193 : reg (bv 128)) => do
      v_10988 <- evaluateAddress v_3192;
      v_10989 <- load v_10988 16;
      v_10990 <- eval (extract v_10989 0 32);
      v_10997 <- eval (extract v_10989 32 64);
      v_11004 <- eval (extract v_10989 64 96);
      v_11011 <- eval (extract v_10989 96 128);
      setRegister (lhs.of_reg v_3193) (concat (mux (ugt v_10990 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10990 (mi (bitwidthMInt v_10990) -1))) v_10990) (concat (mux (ugt v_10997 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10997 (mi (bitwidthMInt v_10997) -1))) v_10997) (concat (mux (ugt v_11004 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11004 (mi (bitwidthMInt v_11004) -1))) v_11004) (mux (ugt v_11011 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11011 (mi (bitwidthMInt v_11011) -1))) v_11011))));
      pure ()
    pat_end;
    pattern fun (v_3201 : Mem) (v_3202 : reg (bv 256)) => do
      v_11022 <- evaluateAddress v_3201;
      v_11023 <- load v_11022 32;
      v_11024 <- eval (extract v_11023 0 32);
      v_11031 <- eval (extract v_11023 32 64);
      v_11038 <- eval (extract v_11023 64 96);
      v_11045 <- eval (extract v_11023 96 128);
      v_11052 <- eval (extract v_11023 128 160);
      v_11059 <- eval (extract v_11023 160 192);
      v_11066 <- eval (extract v_11023 192 224);
      v_11073 <- eval (extract v_11023 224 256);
      setRegister (lhs.of_reg v_3202) (concat (mux (ugt v_11024 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11024 (mi (bitwidthMInt v_11024) -1))) v_11024) (concat (mux (ugt v_11031 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11031 (mi (bitwidthMInt v_11031) -1))) v_11031) (concat (mux (ugt v_11038 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11038 (mi (bitwidthMInt v_11038) -1))) v_11038) (concat (mux (ugt v_11045 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11045 (mi (bitwidthMInt v_11045) -1))) v_11045) (concat (mux (ugt v_11052 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11052 (mi (bitwidthMInt v_11052) -1))) v_11052) (concat (mux (ugt v_11059 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11059 (mi (bitwidthMInt v_11059) -1))) v_11059) (concat (mux (ugt v_11066 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11066 (mi (bitwidthMInt v_11066) -1))) v_11066) (mux (ugt v_11073 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_11073 (mi (bitwidthMInt v_11073) -1))) v_11073))))))));
      pure ()
    pat_end
