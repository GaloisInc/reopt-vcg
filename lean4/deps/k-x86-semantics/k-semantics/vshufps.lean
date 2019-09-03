def vshufps1 : instruction :=
  definst "vshufps" $ do
    pattern fun (v_2932 : imm int) (v_2934 : reg (bv 128)) (v_2935 : reg (bv 128)) (v_2936 : reg (bv 128)) => do
      v_6991 <- eval (handleImmediateWithSignExtend v_2932 8 8);
      v_6995 <- eval (eq (extract v_6991 0 1) (expression.bv_nat 1 1));
      v_6996 <- getRegister v_2934;
      v_6997 <- eval (extract v_6996 0 32);
      v_6998 <- eval (extract v_6996 64 96);
      v_7000 <- eval (extract v_6996 32 64);
      v_7001 <- eval (extract v_6996 96 128);
      v_7007 <- eval (eq (extract v_6991 2 3) (expression.bv_nat 1 1));
      v_7014 <- eval (eq (extract v_6991 4 5) (expression.bv_nat 1 1));
      v_7015 <- getRegister v_2935;
      v_7016 <- eval (extract v_7015 0 32);
      v_7017 <- eval (extract v_7015 64 96);
      v_7019 <- eval (extract v_7015 32 64);
      v_7020 <- eval (extract v_7015 96 128);
      v_7026 <- eval (eq (extract v_6991 6 7) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2936) (concat (mux (eq (extract v_6991 1 2) (expression.bv_nat 1 1)) (mux v_6995 v_6997 v_6998) (mux v_6995 v_7000 v_7001)) (concat (mux (eq (extract v_6991 3 4) (expression.bv_nat 1 1)) (mux v_7007 v_6997 v_6998) (mux v_7007 v_7000 v_7001)) (concat (mux (eq (extract v_6991 5 6) (expression.bv_nat 1 1)) (mux v_7014 v_7016 v_7017) (mux v_7014 v_7019 v_7020)) (mux (eq (extract v_6991 7 8) (expression.bv_nat 1 1)) (mux v_7026 v_7016 v_7017) (mux v_7026 v_7019 v_7020)))));
      pure ()
    pat_end;
    pattern fun (v_2945 : imm int) (v_2946 : reg (bv 256)) (v_2947 : reg (bv 256)) (v_2948 : reg (bv 256)) => do
      v_7040 <- eval (handleImmediateWithSignExtend v_2945 8 8);
      v_7042 <- eval (eq (extract v_7040 1 2) (expression.bv_nat 1 1));
      v_7044 <- eval (eq (extract v_7040 0 1) (expression.bv_nat 1 1));
      v_7045 <- getRegister v_2946;
      v_7046 <- eval (extract v_7045 0 32);
      v_7047 <- eval (extract v_7045 64 96);
      v_7049 <- eval (extract v_7045 32 64);
      v_7050 <- eval (extract v_7045 96 128);
      v_7054 <- eval (eq (extract v_7040 3 4) (expression.bv_nat 1 1));
      v_7056 <- eval (eq (extract v_7040 2 3) (expression.bv_nat 1 1));
      v_7061 <- eval (eq (extract v_7040 5 6) (expression.bv_nat 1 1));
      v_7063 <- eval (eq (extract v_7040 4 5) (expression.bv_nat 1 1));
      v_7064 <- getRegister v_2947;
      v_7065 <- eval (extract v_7064 0 32);
      v_7066 <- eval (extract v_7064 64 96);
      v_7068 <- eval (extract v_7064 32 64);
      v_7069 <- eval (extract v_7064 96 128);
      v_7073 <- eval (eq (extract v_7040 7 8) (expression.bv_nat 1 1));
      v_7075 <- eval (eq (extract v_7040 6 7) (expression.bv_nat 1 1));
      v_7079 <- eval (extract v_7045 128 160);
      v_7080 <- eval (extract v_7045 192 224);
      v_7082 <- eval (extract v_7045 160 192);
      v_7083 <- eval (extract v_7045 224 256);
      v_7089 <- eval (extract v_7064 128 160);
      v_7090 <- eval (extract v_7064 192 224);
      v_7092 <- eval (extract v_7064 160 192);
      v_7093 <- eval (extract v_7064 224 256);
      setRegister (lhs.of_reg v_2948) (concat (mux v_7042 (mux v_7044 v_7046 v_7047) (mux v_7044 v_7049 v_7050)) (concat (mux v_7054 (mux v_7056 v_7046 v_7047) (mux v_7056 v_7049 v_7050)) (concat (mux v_7061 (mux v_7063 v_7065 v_7066) (mux v_7063 v_7068 v_7069)) (concat (mux v_7073 (mux v_7075 v_7065 v_7066) (mux v_7075 v_7068 v_7069)) (concat (mux v_7042 (mux v_7044 v_7079 v_7080) (mux v_7044 v_7082 v_7083)) (concat (mux v_7054 (mux v_7056 v_7079 v_7080) (mux v_7056 v_7082 v_7083)) (concat (mux v_7061 (mux v_7063 v_7089 v_7090) (mux v_7063 v_7092 v_7093)) (mux v_7073 (mux v_7075 v_7089 v_7090) (mux v_7075 v_7092 v_7093)))))))));
      pure ()
    pat_end;
    pattern fun (v_2926 : imm int) (v_2927 : Mem) (v_2928 : reg (bv 128)) (v_2929 : reg (bv 128)) => do
      v_13189 <- eval (handleImmediateWithSignExtend v_2926 8 8);
      v_13193 <- eval (eq (extract v_13189 0 1) (expression.bv_nat 1 1));
      v_13194 <- evaluateAddress v_2927;
      v_13195 <- load v_13194 16;
      v_13196 <- eval (extract v_13195 0 32);
      v_13197 <- eval (extract v_13195 64 96);
      v_13199 <- eval (extract v_13195 32 64);
      v_13200 <- eval (extract v_13195 96 128);
      v_13206 <- eval (eq (extract v_13189 2 3) (expression.bv_nat 1 1));
      v_13213 <- eval (eq (extract v_13189 4 5) (expression.bv_nat 1 1));
      v_13214 <- getRegister v_2928;
      v_13215 <- eval (extract v_13214 0 32);
      v_13216 <- eval (extract v_13214 64 96);
      v_13218 <- eval (extract v_13214 32 64);
      v_13219 <- eval (extract v_13214 96 128);
      v_13225 <- eval (eq (extract v_13189 6 7) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2929) (concat (mux (eq (extract v_13189 1 2) (expression.bv_nat 1 1)) (mux v_13193 v_13196 v_13197) (mux v_13193 v_13199 v_13200)) (concat (mux (eq (extract v_13189 3 4) (expression.bv_nat 1 1)) (mux v_13206 v_13196 v_13197) (mux v_13206 v_13199 v_13200)) (concat (mux (eq (extract v_13189 5 6) (expression.bv_nat 1 1)) (mux v_13213 v_13215 v_13216) (mux v_13213 v_13218 v_13219)) (mux (eq (extract v_13189 7 8) (expression.bv_nat 1 1)) (mux v_13225 v_13215 v_13216) (mux v_13225 v_13218 v_13219)))));
      pure ()
    pat_end;
    pattern fun (v_2939 : imm int) (v_2940 : Mem) (v_2941 : reg (bv 256)) (v_2942 : reg (bv 256)) => do
      v_13233 <- eval (handleImmediateWithSignExtend v_2939 8 8);
      v_13235 <- eval (eq (extract v_13233 1 2) (expression.bv_nat 1 1));
      v_13237 <- eval (eq (extract v_13233 0 1) (expression.bv_nat 1 1));
      v_13238 <- evaluateAddress v_2940;
      v_13239 <- load v_13238 32;
      v_13240 <- eval (extract v_13239 0 32);
      v_13241 <- eval (extract v_13239 64 96);
      v_13243 <- eval (extract v_13239 32 64);
      v_13244 <- eval (extract v_13239 96 128);
      v_13248 <- eval (eq (extract v_13233 3 4) (expression.bv_nat 1 1));
      v_13250 <- eval (eq (extract v_13233 2 3) (expression.bv_nat 1 1));
      v_13255 <- eval (eq (extract v_13233 5 6) (expression.bv_nat 1 1));
      v_13257 <- eval (eq (extract v_13233 4 5) (expression.bv_nat 1 1));
      v_13258 <- getRegister v_2941;
      v_13259 <- eval (extract v_13258 0 32);
      v_13260 <- eval (extract v_13258 64 96);
      v_13262 <- eval (extract v_13258 32 64);
      v_13263 <- eval (extract v_13258 96 128);
      v_13267 <- eval (eq (extract v_13233 7 8) (expression.bv_nat 1 1));
      v_13269 <- eval (eq (extract v_13233 6 7) (expression.bv_nat 1 1));
      v_13273 <- eval (extract v_13239 128 160);
      v_13274 <- eval (extract v_13239 192 224);
      v_13276 <- eval (extract v_13239 160 192);
      v_13277 <- eval (extract v_13239 224 256);
      v_13283 <- eval (extract v_13258 128 160);
      v_13284 <- eval (extract v_13258 192 224);
      v_13286 <- eval (extract v_13258 160 192);
      v_13287 <- eval (extract v_13258 224 256);
      setRegister (lhs.of_reg v_2942) (concat (mux v_13235 (mux v_13237 v_13240 v_13241) (mux v_13237 v_13243 v_13244)) (concat (mux v_13248 (mux v_13250 v_13240 v_13241) (mux v_13250 v_13243 v_13244)) (concat (mux v_13255 (mux v_13257 v_13259 v_13260) (mux v_13257 v_13262 v_13263)) (concat (mux v_13267 (mux v_13269 v_13259 v_13260) (mux v_13269 v_13262 v_13263)) (concat (mux v_13235 (mux v_13237 v_13273 v_13274) (mux v_13237 v_13276 v_13277)) (concat (mux v_13248 (mux v_13250 v_13273 v_13274) (mux v_13250 v_13276 v_13277)) (concat (mux v_13255 (mux v_13257 v_13283 v_13284) (mux v_13257 v_13286 v_13287)) (mux v_13267 (mux v_13269 v_13283 v_13284) (mux v_13269 v_13286 v_13287)))))))));
      pure ()
    pat_end
