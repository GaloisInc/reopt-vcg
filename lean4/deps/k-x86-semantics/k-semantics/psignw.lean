def psignw1 : instruction :=
  definst "psignw" $ do
    pattern fun (v_3041 : reg (bv 128)) (v_3042 : reg (bv 128)) => do
      v_7484 <- getRegister v_3041;
      v_7485 <- eval (extract v_7484 0 16);
      v_7487 <- getRegister v_3042;
      v_7488 <- eval (extract v_7487 0 16);
      v_7494 <- eval (extract v_7484 16 32);
      v_7496 <- eval (extract v_7487 16 32);
      v_7502 <- eval (extract v_7484 32 48);
      v_7504 <- eval (extract v_7487 32 48);
      v_7510 <- eval (extract v_7484 48 64);
      v_7512 <- eval (extract v_7487 48 64);
      v_7518 <- eval (extract v_7484 64 80);
      v_7520 <- eval (extract v_7487 64 80);
      v_7526 <- eval (extract v_7484 80 96);
      v_7528 <- eval (extract v_7487 80 96);
      v_7534 <- eval (extract v_7484 96 112);
      v_7536 <- eval (extract v_7487 96 112);
      v_7542 <- eval (extract v_7484 112 128);
      v_7544 <- eval (extract v_7487 112 128);
      setRegister (lhs.of_reg v_3042) (concat (mux (sgt v_7485 (expression.bv_nat 16 0)) v_7488 (mux (eq v_7485 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7488 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7494 (expression.bv_nat 16 0)) v_7496 (mux (eq v_7494 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7496 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7502 (expression.bv_nat 16 0)) v_7504 (mux (eq v_7502 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7504 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7510 (expression.bv_nat 16 0)) v_7512 (mux (eq v_7510 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7512 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7518 (expression.bv_nat 16 0)) v_7520 (mux (eq v_7518 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7520 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7526 (expression.bv_nat 16 0)) v_7528 (mux (eq v_7526 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7528 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7534 (expression.bv_nat 16 0)) v_7536 (mux (eq v_7534 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7536 (expression.bv_nat 16 65535))))) (mux (sgt v_7542 (expression.bv_nat 16 0)) v_7544 (mux (eq v_7542 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7544 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3037 : Mem) (v_3038 : reg (bv 128)) => do
      v_14140 <- evaluateAddress v_3037;
      v_14141 <- load v_14140 16;
      v_14142 <- eval (extract v_14141 0 16);
      v_14144 <- getRegister v_3038;
      v_14145 <- eval (extract v_14144 0 16);
      v_14151 <- eval (extract v_14141 16 32);
      v_14153 <- eval (extract v_14144 16 32);
      v_14159 <- eval (extract v_14141 32 48);
      v_14161 <- eval (extract v_14144 32 48);
      v_14167 <- eval (extract v_14141 48 64);
      v_14169 <- eval (extract v_14144 48 64);
      v_14175 <- eval (extract v_14141 64 80);
      v_14177 <- eval (extract v_14144 64 80);
      v_14183 <- eval (extract v_14141 80 96);
      v_14185 <- eval (extract v_14144 80 96);
      v_14191 <- eval (extract v_14141 96 112);
      v_14193 <- eval (extract v_14144 96 112);
      v_14199 <- eval (extract v_14141 112 128);
      v_14201 <- eval (extract v_14144 112 128);
      setRegister (lhs.of_reg v_3038) (concat (mux (sgt v_14142 (expression.bv_nat 16 0)) v_14145 (mux (eq v_14142 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14145 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14151 (expression.bv_nat 16 0)) v_14153 (mux (eq v_14151 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14153 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14159 (expression.bv_nat 16 0)) v_14161 (mux (eq v_14159 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14161 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14167 (expression.bv_nat 16 0)) v_14169 (mux (eq v_14167 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14169 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14175 (expression.bv_nat 16 0)) v_14177 (mux (eq v_14175 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14177 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14183 (expression.bv_nat 16 0)) v_14185 (mux (eq v_14183 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14185 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14191 (expression.bv_nat 16 0)) v_14193 (mux (eq v_14191 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14193 (expression.bv_nat 16 65535))))) (mux (sgt v_14199 (expression.bv_nat 16 0)) v_14201 (mux (eq v_14199 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14201 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end
