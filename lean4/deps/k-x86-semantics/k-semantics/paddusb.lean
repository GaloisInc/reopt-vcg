def paddusb1 : instruction :=
  definst "paddusb" $ do
    pattern fun (v_3219 : reg (bv 128)) (v_3220 : reg (bv 128)) => do
      v_6000 <- getRegister v_3220;
      v_6003 <- getRegister v_3219;
      v_6006 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 0 8)) (concat (expression.bv_nat 1 0) (extract v_6003 0 8)));
      v_6014 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 8 16)) (concat (expression.bv_nat 1 0) (extract v_6003 8 16)));
      v_6022 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 16 24)) (concat (expression.bv_nat 1 0) (extract v_6003 16 24)));
      v_6030 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 24 32)) (concat (expression.bv_nat 1 0) (extract v_6003 24 32)));
      v_6038 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 32 40)) (concat (expression.bv_nat 1 0) (extract v_6003 32 40)));
      v_6046 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 40 48)) (concat (expression.bv_nat 1 0) (extract v_6003 40 48)));
      v_6054 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 48 56)) (concat (expression.bv_nat 1 0) (extract v_6003 48 56)));
      v_6062 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 56 64)) (concat (expression.bv_nat 1 0) (extract v_6003 56 64)));
      v_6070 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 64 72)) (concat (expression.bv_nat 1 0) (extract v_6003 64 72)));
      v_6078 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 72 80)) (concat (expression.bv_nat 1 0) (extract v_6003 72 80)));
      v_6086 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 80 88)) (concat (expression.bv_nat 1 0) (extract v_6003 80 88)));
      v_6094 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 88 96)) (concat (expression.bv_nat 1 0) (extract v_6003 88 96)));
      v_6102 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 96 104)) (concat (expression.bv_nat 1 0) (extract v_6003 96 104)));
      v_6110 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 104 112)) (concat (expression.bv_nat 1 0) (extract v_6003 104 112)));
      v_6118 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 112 120)) (concat (expression.bv_nat 1 0) (extract v_6003 112 120)));
      v_6126 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6000 120 128)) (concat (expression.bv_nat 1 0) (extract v_6003 120 128)));
      setRegister (lhs.of_reg v_3220) (concat (mux (isBitSet v_6006 0) (expression.bv_nat 8 255) (extract v_6006 1 9)) (concat (mux (isBitSet v_6014 0) (expression.bv_nat 8 255) (extract v_6014 1 9)) (concat (mux (isBitSet v_6022 0) (expression.bv_nat 8 255) (extract v_6022 1 9)) (concat (mux (isBitSet v_6030 0) (expression.bv_nat 8 255) (extract v_6030 1 9)) (concat (mux (isBitSet v_6038 0) (expression.bv_nat 8 255) (extract v_6038 1 9)) (concat (mux (isBitSet v_6046 0) (expression.bv_nat 8 255) (extract v_6046 1 9)) (concat (mux (isBitSet v_6054 0) (expression.bv_nat 8 255) (extract v_6054 1 9)) (concat (mux (isBitSet v_6062 0) (expression.bv_nat 8 255) (extract v_6062 1 9)) (concat (mux (isBitSet v_6070 0) (expression.bv_nat 8 255) (extract v_6070 1 9)) (concat (mux (isBitSet v_6078 0) (expression.bv_nat 8 255) (extract v_6078 1 9)) (concat (mux (isBitSet v_6086 0) (expression.bv_nat 8 255) (extract v_6086 1 9)) (concat (mux (isBitSet v_6094 0) (expression.bv_nat 8 255) (extract v_6094 1 9)) (concat (mux (isBitSet v_6102 0) (expression.bv_nat 8 255) (extract v_6102 1 9)) (concat (mux (isBitSet v_6110 0) (expression.bv_nat 8 255) (extract v_6110 1 9)) (concat (mux (isBitSet v_6118 0) (expression.bv_nat 8 255) (extract v_6118 1 9)) (mux (isBitSet v_6126 0) (expression.bv_nat 8 255) (extract v_6126 1 9)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3214 : Mem) (v_3215 : reg (bv 128)) => do
      v_9920 <- getRegister v_3215;
      v_9923 <- evaluateAddress v_3214;
      v_9924 <- load v_9923 16;
      v_9927 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 0 8)) (concat (expression.bv_nat 1 0) (extract v_9924 0 8)));
      v_9935 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 8 16)) (concat (expression.bv_nat 1 0) (extract v_9924 8 16)));
      v_9943 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 16 24)) (concat (expression.bv_nat 1 0) (extract v_9924 16 24)));
      v_9951 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 24 32)) (concat (expression.bv_nat 1 0) (extract v_9924 24 32)));
      v_9959 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 32 40)) (concat (expression.bv_nat 1 0) (extract v_9924 32 40)));
      v_9967 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 40 48)) (concat (expression.bv_nat 1 0) (extract v_9924 40 48)));
      v_9975 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 48 56)) (concat (expression.bv_nat 1 0) (extract v_9924 48 56)));
      v_9983 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 56 64)) (concat (expression.bv_nat 1 0) (extract v_9924 56 64)));
      v_9991 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 64 72)) (concat (expression.bv_nat 1 0) (extract v_9924 64 72)));
      v_9999 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 72 80)) (concat (expression.bv_nat 1 0) (extract v_9924 72 80)));
      v_10007 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 80 88)) (concat (expression.bv_nat 1 0) (extract v_9924 80 88)));
      v_10015 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 88 96)) (concat (expression.bv_nat 1 0) (extract v_9924 88 96)));
      v_10023 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 96 104)) (concat (expression.bv_nat 1 0) (extract v_9924 96 104)));
      v_10031 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 104 112)) (concat (expression.bv_nat 1 0) (extract v_9924 104 112)));
      v_10039 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 112 120)) (concat (expression.bv_nat 1 0) (extract v_9924 112 120)));
      v_10047 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9920 120 128)) (concat (expression.bv_nat 1 0) (extract v_9924 120 128)));
      setRegister (lhs.of_reg v_3215) (concat (mux (isBitSet v_9927 0) (expression.bv_nat 8 255) (extract v_9927 1 9)) (concat (mux (isBitSet v_9935 0) (expression.bv_nat 8 255) (extract v_9935 1 9)) (concat (mux (isBitSet v_9943 0) (expression.bv_nat 8 255) (extract v_9943 1 9)) (concat (mux (isBitSet v_9951 0) (expression.bv_nat 8 255) (extract v_9951 1 9)) (concat (mux (isBitSet v_9959 0) (expression.bv_nat 8 255) (extract v_9959 1 9)) (concat (mux (isBitSet v_9967 0) (expression.bv_nat 8 255) (extract v_9967 1 9)) (concat (mux (isBitSet v_9975 0) (expression.bv_nat 8 255) (extract v_9975 1 9)) (concat (mux (isBitSet v_9983 0) (expression.bv_nat 8 255) (extract v_9983 1 9)) (concat (mux (isBitSet v_9991 0) (expression.bv_nat 8 255) (extract v_9991 1 9)) (concat (mux (isBitSet v_9999 0) (expression.bv_nat 8 255) (extract v_9999 1 9)) (concat (mux (isBitSet v_10007 0) (expression.bv_nat 8 255) (extract v_10007 1 9)) (concat (mux (isBitSet v_10015 0) (expression.bv_nat 8 255) (extract v_10015 1 9)) (concat (mux (isBitSet v_10023 0) (expression.bv_nat 8 255) (extract v_10023 1 9)) (concat (mux (isBitSet v_10031 0) (expression.bv_nat 8 255) (extract v_10031 1 9)) (concat (mux (isBitSet v_10039 0) (expression.bv_nat 8 255) (extract v_10039 1 9)) (mux (isBitSet v_10047 0) (expression.bv_nat 8 255) (extract v_10047 1 9)))))))))))))))));
      pure ()
    pat_end
