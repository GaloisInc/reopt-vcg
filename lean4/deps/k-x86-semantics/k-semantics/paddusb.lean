def paddusb1 : instruction :=
  definst "paddusb" $ do
    pattern fun (v_3244 : reg (bv 128)) (v_3245 : reg (bv 128)) => do
      v_6027 <- getRegister v_3245;
      v_6030 <- getRegister v_3244;
      v_6033 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 0 8)) (concat (expression.bv_nat 1 0) (extract v_6030 0 8)));
      v_6041 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 8 16)) (concat (expression.bv_nat 1 0) (extract v_6030 8 16)));
      v_6049 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 16 24)) (concat (expression.bv_nat 1 0) (extract v_6030 16 24)));
      v_6057 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 24 32)) (concat (expression.bv_nat 1 0) (extract v_6030 24 32)));
      v_6065 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 32 40)) (concat (expression.bv_nat 1 0) (extract v_6030 32 40)));
      v_6073 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 40 48)) (concat (expression.bv_nat 1 0) (extract v_6030 40 48)));
      v_6081 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 48 56)) (concat (expression.bv_nat 1 0) (extract v_6030 48 56)));
      v_6089 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 56 64)) (concat (expression.bv_nat 1 0) (extract v_6030 56 64)));
      v_6097 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 64 72)) (concat (expression.bv_nat 1 0) (extract v_6030 64 72)));
      v_6105 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 72 80)) (concat (expression.bv_nat 1 0) (extract v_6030 72 80)));
      v_6113 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 80 88)) (concat (expression.bv_nat 1 0) (extract v_6030 80 88)));
      v_6121 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 88 96)) (concat (expression.bv_nat 1 0) (extract v_6030 88 96)));
      v_6129 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 96 104)) (concat (expression.bv_nat 1 0) (extract v_6030 96 104)));
      v_6137 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 104 112)) (concat (expression.bv_nat 1 0) (extract v_6030 104 112)));
      v_6145 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 112 120)) (concat (expression.bv_nat 1 0) (extract v_6030 112 120)));
      v_6153 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6027 120 128)) (concat (expression.bv_nat 1 0) (extract v_6030 120 128)));
      setRegister (lhs.of_reg v_3245) (concat (mux (isBitSet v_6033 0) (expression.bv_nat 8 255) (extract v_6033 1 9)) (concat (mux (isBitSet v_6041 0) (expression.bv_nat 8 255) (extract v_6041 1 9)) (concat (mux (isBitSet v_6049 0) (expression.bv_nat 8 255) (extract v_6049 1 9)) (concat (mux (isBitSet v_6057 0) (expression.bv_nat 8 255) (extract v_6057 1 9)) (concat (mux (isBitSet v_6065 0) (expression.bv_nat 8 255) (extract v_6065 1 9)) (concat (mux (isBitSet v_6073 0) (expression.bv_nat 8 255) (extract v_6073 1 9)) (concat (mux (isBitSet v_6081 0) (expression.bv_nat 8 255) (extract v_6081 1 9)) (concat (mux (isBitSet v_6089 0) (expression.bv_nat 8 255) (extract v_6089 1 9)) (concat (mux (isBitSet v_6097 0) (expression.bv_nat 8 255) (extract v_6097 1 9)) (concat (mux (isBitSet v_6105 0) (expression.bv_nat 8 255) (extract v_6105 1 9)) (concat (mux (isBitSet v_6113 0) (expression.bv_nat 8 255) (extract v_6113 1 9)) (concat (mux (isBitSet v_6121 0) (expression.bv_nat 8 255) (extract v_6121 1 9)) (concat (mux (isBitSet v_6129 0) (expression.bv_nat 8 255) (extract v_6129 1 9)) (concat (mux (isBitSet v_6137 0) (expression.bv_nat 8 255) (extract v_6137 1 9)) (concat (mux (isBitSet v_6145 0) (expression.bv_nat 8 255) (extract v_6145 1 9)) (mux (isBitSet v_6153 0) (expression.bv_nat 8 255) (extract v_6153 1 9)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3240 : Mem) (v_3241 : reg (bv 128)) => do
      v_9947 <- getRegister v_3241;
      v_9950 <- evaluateAddress v_3240;
      v_9951 <- load v_9950 16;
      v_9954 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 0 8)) (concat (expression.bv_nat 1 0) (extract v_9951 0 8)));
      v_9962 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 8 16)) (concat (expression.bv_nat 1 0) (extract v_9951 8 16)));
      v_9970 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 16 24)) (concat (expression.bv_nat 1 0) (extract v_9951 16 24)));
      v_9978 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 24 32)) (concat (expression.bv_nat 1 0) (extract v_9951 24 32)));
      v_9986 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 32 40)) (concat (expression.bv_nat 1 0) (extract v_9951 32 40)));
      v_9994 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 40 48)) (concat (expression.bv_nat 1 0) (extract v_9951 40 48)));
      v_10002 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 48 56)) (concat (expression.bv_nat 1 0) (extract v_9951 48 56)));
      v_10010 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 56 64)) (concat (expression.bv_nat 1 0) (extract v_9951 56 64)));
      v_10018 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 64 72)) (concat (expression.bv_nat 1 0) (extract v_9951 64 72)));
      v_10026 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 72 80)) (concat (expression.bv_nat 1 0) (extract v_9951 72 80)));
      v_10034 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 80 88)) (concat (expression.bv_nat 1 0) (extract v_9951 80 88)));
      v_10042 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 88 96)) (concat (expression.bv_nat 1 0) (extract v_9951 88 96)));
      v_10050 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 96 104)) (concat (expression.bv_nat 1 0) (extract v_9951 96 104)));
      v_10058 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 104 112)) (concat (expression.bv_nat 1 0) (extract v_9951 104 112)));
      v_10066 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 112 120)) (concat (expression.bv_nat 1 0) (extract v_9951 112 120)));
      v_10074 <- eval (add (concat (expression.bv_nat 1 0) (extract v_9947 120 128)) (concat (expression.bv_nat 1 0) (extract v_9951 120 128)));
      setRegister (lhs.of_reg v_3241) (concat (mux (isBitSet v_9954 0) (expression.bv_nat 8 255) (extract v_9954 1 9)) (concat (mux (isBitSet v_9962 0) (expression.bv_nat 8 255) (extract v_9962 1 9)) (concat (mux (isBitSet v_9970 0) (expression.bv_nat 8 255) (extract v_9970 1 9)) (concat (mux (isBitSet v_9978 0) (expression.bv_nat 8 255) (extract v_9978 1 9)) (concat (mux (isBitSet v_9986 0) (expression.bv_nat 8 255) (extract v_9986 1 9)) (concat (mux (isBitSet v_9994 0) (expression.bv_nat 8 255) (extract v_9994 1 9)) (concat (mux (isBitSet v_10002 0) (expression.bv_nat 8 255) (extract v_10002 1 9)) (concat (mux (isBitSet v_10010 0) (expression.bv_nat 8 255) (extract v_10010 1 9)) (concat (mux (isBitSet v_10018 0) (expression.bv_nat 8 255) (extract v_10018 1 9)) (concat (mux (isBitSet v_10026 0) (expression.bv_nat 8 255) (extract v_10026 1 9)) (concat (mux (isBitSet v_10034 0) (expression.bv_nat 8 255) (extract v_10034 1 9)) (concat (mux (isBitSet v_10042 0) (expression.bv_nat 8 255) (extract v_10042 1 9)) (concat (mux (isBitSet v_10050 0) (expression.bv_nat 8 255) (extract v_10050 1 9)) (concat (mux (isBitSet v_10058 0) (expression.bv_nat 8 255) (extract v_10058 1 9)) (concat (mux (isBitSet v_10066 0) (expression.bv_nat 8 255) (extract v_10066 1 9)) (mux (isBitSet v_10074 0) (expression.bv_nat 8 255) (extract v_10074 1 9)))))))))))))))));
      pure ()
    pat_end
