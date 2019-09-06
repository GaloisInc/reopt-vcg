def paddusw1 : instruction :=
  definst "paddusw" $ do
    pattern fun (v_3253 : reg (bv 128)) (v_3254 : reg (bv 128)) => do
      v_6177 <- getRegister v_3254;
      v_6180 <- getRegister v_3253;
      v_6183 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6177 0 16)) (concat (expression.bv_nat 1 0) (extract v_6180 0 16)));
      v_6191 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6177 16 32)) (concat (expression.bv_nat 1 0) (extract v_6180 16 32)));
      v_6199 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6177 32 48)) (concat (expression.bv_nat 1 0) (extract v_6180 32 48)));
      v_6207 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6177 48 64)) (concat (expression.bv_nat 1 0) (extract v_6180 48 64)));
      v_6215 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6177 64 80)) (concat (expression.bv_nat 1 0) (extract v_6180 64 80)));
      v_6223 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6177 80 96)) (concat (expression.bv_nat 1 0) (extract v_6180 80 96)));
      v_6231 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6177 96 112)) (concat (expression.bv_nat 1 0) (extract v_6180 96 112)));
      v_6239 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6177 112 128)) (concat (expression.bv_nat 1 0) (extract v_6180 112 128)));
      setRegister (lhs.of_reg v_3254) (concat (mux (isBitSet v_6183 0) (expression.bv_nat 16 65535) (extract v_6183 1 17)) (concat (mux (isBitSet v_6191 0) (expression.bv_nat 16 65535) (extract v_6191 1 17)) (concat (mux (isBitSet v_6199 0) (expression.bv_nat 16 65535) (extract v_6199 1 17)) (concat (mux (isBitSet v_6207 0) (expression.bv_nat 16 65535) (extract v_6207 1 17)) (concat (mux (isBitSet v_6215 0) (expression.bv_nat 16 65535) (extract v_6215 1 17)) (concat (mux (isBitSet v_6223 0) (expression.bv_nat 16 65535) (extract v_6223 1 17)) (concat (mux (isBitSet v_6231 0) (expression.bv_nat 16 65535) (extract v_6231 1 17)) (mux (isBitSet v_6239 0) (expression.bv_nat 16 65535) (extract v_6239 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_3249 : Mem) (v_3250 : reg (bv 128)) => do
      v_10094 <- getRegister v_3250;
      v_10097 <- evaluateAddress v_3249;
      v_10098 <- load v_10097 16;
      v_10101 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10094 0 16)) (concat (expression.bv_nat 1 0) (extract v_10098 0 16)));
      v_10109 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10094 16 32)) (concat (expression.bv_nat 1 0) (extract v_10098 16 32)));
      v_10117 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10094 32 48)) (concat (expression.bv_nat 1 0) (extract v_10098 32 48)));
      v_10125 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10094 48 64)) (concat (expression.bv_nat 1 0) (extract v_10098 48 64)));
      v_10133 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10094 64 80)) (concat (expression.bv_nat 1 0) (extract v_10098 64 80)));
      v_10141 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10094 80 96)) (concat (expression.bv_nat 1 0) (extract v_10098 80 96)));
      v_10149 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10094 96 112)) (concat (expression.bv_nat 1 0) (extract v_10098 96 112)));
      v_10157 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10094 112 128)) (concat (expression.bv_nat 1 0) (extract v_10098 112 128)));
      setRegister (lhs.of_reg v_3250) (concat (mux (isBitSet v_10101 0) (expression.bv_nat 16 65535) (extract v_10101 1 17)) (concat (mux (isBitSet v_10109 0) (expression.bv_nat 16 65535) (extract v_10109 1 17)) (concat (mux (isBitSet v_10117 0) (expression.bv_nat 16 65535) (extract v_10117 1 17)) (concat (mux (isBitSet v_10125 0) (expression.bv_nat 16 65535) (extract v_10125 1 17)) (concat (mux (isBitSet v_10133 0) (expression.bv_nat 16 65535) (extract v_10133 1 17)) (concat (mux (isBitSet v_10141 0) (expression.bv_nat 16 65535) (extract v_10141 1 17)) (concat (mux (isBitSet v_10149 0) (expression.bv_nat 16 65535) (extract v_10149 1 17)) (mux (isBitSet v_10157 0) (expression.bv_nat 16 65535) (extract v_10157 1 17)))))))));
      pure ()
    pat_end
