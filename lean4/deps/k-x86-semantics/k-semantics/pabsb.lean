def pabsb1 : instruction :=
  definst "pabsb" $ do
    pattern fun (v_3111 : reg (bv 128)) (v_3112 : reg (bv 128)) => do
      v_5075 <- getRegister v_3111;
      v_5076 <- eval (extract v_5075 0 8);
      v_5081 <- eval (extract v_5075 8 16);
      v_5086 <- eval (extract v_5075 16 24);
      v_5091 <- eval (extract v_5075 24 32);
      v_5096 <- eval (extract v_5075 32 40);
      v_5101 <- eval (extract v_5075 40 48);
      v_5106 <- eval (extract v_5075 48 56);
      v_5111 <- eval (extract v_5075 56 64);
      v_5116 <- eval (extract v_5075 64 72);
      v_5121 <- eval (extract v_5075 72 80);
      v_5126 <- eval (extract v_5075 80 88);
      v_5131 <- eval (extract v_5075 88 96);
      v_5136 <- eval (extract v_5075 96 104);
      v_5141 <- eval (extract v_5075 104 112);
      v_5146 <- eval (extract v_5075 112 120);
      v_5151 <- eval (extract v_5075 120 128);
      setRegister (lhs.of_reg v_3112) (concat (mux (ugt v_5076 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5076 (expression.bv_nat 8 255))) v_5076) (concat (mux (ugt v_5081 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5081 (expression.bv_nat 8 255))) v_5081) (concat (mux (ugt v_5086 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5086 (expression.bv_nat 8 255))) v_5086) (concat (mux (ugt v_5091 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5091 (expression.bv_nat 8 255))) v_5091) (concat (mux (ugt v_5096 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5096 (expression.bv_nat 8 255))) v_5096) (concat (mux (ugt v_5101 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5101 (expression.bv_nat 8 255))) v_5101) (concat (mux (ugt v_5106 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5106 (expression.bv_nat 8 255))) v_5106) (concat (mux (ugt v_5111 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5111 (expression.bv_nat 8 255))) v_5111) (concat (mux (ugt v_5116 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5116 (expression.bv_nat 8 255))) v_5116) (concat (mux (ugt v_5121 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5121 (expression.bv_nat 8 255))) v_5121) (concat (mux (ugt v_5126 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5126 (expression.bv_nat 8 255))) v_5126) (concat (mux (ugt v_5131 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5131 (expression.bv_nat 8 255))) v_5131) (concat (mux (ugt v_5136 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5136 (expression.bv_nat 8 255))) v_5136) (concat (mux (ugt v_5141 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5141 (expression.bv_nat 8 255))) v_5141) (concat (mux (ugt v_5146 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5146 (expression.bv_nat 8 255))) v_5146) (mux (ugt v_5151 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5151 (expression.bv_nat 8 255))) v_5151))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3106 : Mem) (v_3107 : reg (bv 128)) => do
      v_9031 <- evaluateAddress v_3106;
      v_9032 <- load v_9031 16;
      v_9033 <- eval (extract v_9032 0 8);
      v_9038 <- eval (extract v_9032 8 16);
      v_9043 <- eval (extract v_9032 16 24);
      v_9048 <- eval (extract v_9032 24 32);
      v_9053 <- eval (extract v_9032 32 40);
      v_9058 <- eval (extract v_9032 40 48);
      v_9063 <- eval (extract v_9032 48 56);
      v_9068 <- eval (extract v_9032 56 64);
      v_9073 <- eval (extract v_9032 64 72);
      v_9078 <- eval (extract v_9032 72 80);
      v_9083 <- eval (extract v_9032 80 88);
      v_9088 <- eval (extract v_9032 88 96);
      v_9093 <- eval (extract v_9032 96 104);
      v_9098 <- eval (extract v_9032 104 112);
      v_9103 <- eval (extract v_9032 112 120);
      v_9108 <- eval (extract v_9032 120 128);
      setRegister (lhs.of_reg v_3107) (concat (mux (ugt v_9033 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9033 (expression.bv_nat 8 255))) v_9033) (concat (mux (ugt v_9038 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9038 (expression.bv_nat 8 255))) v_9038) (concat (mux (ugt v_9043 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9043 (expression.bv_nat 8 255))) v_9043) (concat (mux (ugt v_9048 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9048 (expression.bv_nat 8 255))) v_9048) (concat (mux (ugt v_9053 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9053 (expression.bv_nat 8 255))) v_9053) (concat (mux (ugt v_9058 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9058 (expression.bv_nat 8 255))) v_9058) (concat (mux (ugt v_9063 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9063 (expression.bv_nat 8 255))) v_9063) (concat (mux (ugt v_9068 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9068 (expression.bv_nat 8 255))) v_9068) (concat (mux (ugt v_9073 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9073 (expression.bv_nat 8 255))) v_9073) (concat (mux (ugt v_9078 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9078 (expression.bv_nat 8 255))) v_9078) (concat (mux (ugt v_9083 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9083 (expression.bv_nat 8 255))) v_9083) (concat (mux (ugt v_9088 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9088 (expression.bv_nat 8 255))) v_9088) (concat (mux (ugt v_9093 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9093 (expression.bv_nat 8 255))) v_9093) (concat (mux (ugt v_9098 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9098 (expression.bv_nat 8 255))) v_9098) (concat (mux (ugt v_9103 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9103 (expression.bv_nat 8 255))) v_9103) (mux (ugt v_9108 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9108 (expression.bv_nat 8 255))) v_9108))))))))))))))));
      pure ()
    pat_end
