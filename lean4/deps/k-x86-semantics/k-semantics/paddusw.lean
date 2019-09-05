def paddusw1 : instruction :=
  definst "paddusw" $ do
    pattern fun (v_3228 : reg (bv 128)) (v_3229 : reg (bv 128)) => do
      v_6150 <- getRegister v_3229;
      v_6153 <- getRegister v_3228;
      v_6156 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6150 0 16)) (concat (expression.bv_nat 1 0) (extract v_6153 0 16)));
      v_6164 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6150 16 32)) (concat (expression.bv_nat 1 0) (extract v_6153 16 32)));
      v_6172 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6150 32 48)) (concat (expression.bv_nat 1 0) (extract v_6153 32 48)));
      v_6180 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6150 48 64)) (concat (expression.bv_nat 1 0) (extract v_6153 48 64)));
      v_6188 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6150 64 80)) (concat (expression.bv_nat 1 0) (extract v_6153 64 80)));
      v_6196 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6150 80 96)) (concat (expression.bv_nat 1 0) (extract v_6153 80 96)));
      v_6204 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6150 96 112)) (concat (expression.bv_nat 1 0) (extract v_6153 96 112)));
      v_6212 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6150 112 128)) (concat (expression.bv_nat 1 0) (extract v_6153 112 128)));
      setRegister (lhs.of_reg v_3229) (concat (mux (isBitSet v_6156 0) (expression.bv_nat 16 65535) (extract v_6156 1 17)) (concat (mux (isBitSet v_6164 0) (expression.bv_nat 16 65535) (extract v_6164 1 17)) (concat (mux (isBitSet v_6172 0) (expression.bv_nat 16 65535) (extract v_6172 1 17)) (concat (mux (isBitSet v_6180 0) (expression.bv_nat 16 65535) (extract v_6180 1 17)) (concat (mux (isBitSet v_6188 0) (expression.bv_nat 16 65535) (extract v_6188 1 17)) (concat (mux (isBitSet v_6196 0) (expression.bv_nat 16 65535) (extract v_6196 1 17)) (concat (mux (isBitSet v_6204 0) (expression.bv_nat 16 65535) (extract v_6204 1 17)) (mux (isBitSet v_6212 0) (expression.bv_nat 16 65535) (extract v_6212 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_3223 : Mem) (v_3224 : reg (bv 128)) => do
      v_10067 <- getRegister v_3224;
      v_10070 <- evaluateAddress v_3223;
      v_10071 <- load v_10070 16;
      v_10074 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10067 0 16)) (concat (expression.bv_nat 1 0) (extract v_10071 0 16)));
      v_10082 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10067 16 32)) (concat (expression.bv_nat 1 0) (extract v_10071 16 32)));
      v_10090 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10067 32 48)) (concat (expression.bv_nat 1 0) (extract v_10071 32 48)));
      v_10098 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10067 48 64)) (concat (expression.bv_nat 1 0) (extract v_10071 48 64)));
      v_10106 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10067 64 80)) (concat (expression.bv_nat 1 0) (extract v_10071 64 80)));
      v_10114 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10067 80 96)) (concat (expression.bv_nat 1 0) (extract v_10071 80 96)));
      v_10122 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10067 96 112)) (concat (expression.bv_nat 1 0) (extract v_10071 96 112)));
      v_10130 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10067 112 128)) (concat (expression.bv_nat 1 0) (extract v_10071 112 128)));
      setRegister (lhs.of_reg v_3224) (concat (mux (isBitSet v_10074 0) (expression.bv_nat 16 65535) (extract v_10074 1 17)) (concat (mux (isBitSet v_10082 0) (expression.bv_nat 16 65535) (extract v_10082 1 17)) (concat (mux (isBitSet v_10090 0) (expression.bv_nat 16 65535) (extract v_10090 1 17)) (concat (mux (isBitSet v_10098 0) (expression.bv_nat 16 65535) (extract v_10098 1 17)) (concat (mux (isBitSet v_10106 0) (expression.bv_nat 16 65535) (extract v_10106 1 17)) (concat (mux (isBitSet v_10114 0) (expression.bv_nat 16 65535) (extract v_10114 1 17)) (concat (mux (isBitSet v_10122 0) (expression.bv_nat 16 65535) (extract v_10122 1 17)) (mux (isBitSet v_10130 0) (expression.bv_nat 16 65535) (extract v_10130 1 17)))))))));
      pure ()
    pat_end
