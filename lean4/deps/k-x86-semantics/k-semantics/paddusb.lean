def paddusb1 : instruction :=
  definst "paddusb" $ do
    pattern fun (v_3156 : reg (bv 128)) (v_3157 : reg (bv 128)) => do
      v_6104 <- getRegister v_3157;
      v_6107 <- getRegister v_3156;
      v_6110 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 0 8)) (concat (expression.bv_nat 1 0) (extract v_6107 0 8)));
      v_6119 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 8 16)) (concat (expression.bv_nat 1 0) (extract v_6107 8 16)));
      v_6128 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 16 24)) (concat (expression.bv_nat 1 0) (extract v_6107 16 24)));
      v_6137 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 24 32)) (concat (expression.bv_nat 1 0) (extract v_6107 24 32)));
      v_6146 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 32 40)) (concat (expression.bv_nat 1 0) (extract v_6107 32 40)));
      v_6155 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 40 48)) (concat (expression.bv_nat 1 0) (extract v_6107 40 48)));
      v_6164 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 48 56)) (concat (expression.bv_nat 1 0) (extract v_6107 48 56)));
      v_6173 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 56 64)) (concat (expression.bv_nat 1 0) (extract v_6107 56 64)));
      v_6182 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 64 72)) (concat (expression.bv_nat 1 0) (extract v_6107 64 72)));
      v_6191 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 72 80)) (concat (expression.bv_nat 1 0) (extract v_6107 72 80)));
      v_6200 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 80 88)) (concat (expression.bv_nat 1 0) (extract v_6107 80 88)));
      v_6209 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 88 96)) (concat (expression.bv_nat 1 0) (extract v_6107 88 96)));
      v_6218 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 96 104)) (concat (expression.bv_nat 1 0) (extract v_6107 96 104)));
      v_6227 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 104 112)) (concat (expression.bv_nat 1 0) (extract v_6107 104 112)));
      v_6236 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 112 120)) (concat (expression.bv_nat 1 0) (extract v_6107 112 120)));
      v_6245 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6104 120 128)) (concat (expression.bv_nat 1 0) (extract v_6107 120 128)));
      setRegister (lhs.of_reg v_3157) (concat (mux (eq (extract v_6110 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6110 1 9)) (concat (mux (eq (extract v_6119 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6119 1 9)) (concat (mux (eq (extract v_6128 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6128 1 9)) (concat (mux (eq (extract v_6137 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6137 1 9)) (concat (mux (eq (extract v_6146 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6146 1 9)) (concat (mux (eq (extract v_6155 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6155 1 9)) (concat (mux (eq (extract v_6164 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6164 1 9)) (concat (mux (eq (extract v_6173 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6173 1 9)) (concat (mux (eq (extract v_6182 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6182 1 9)) (concat (mux (eq (extract v_6191 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6191 1 9)) (concat (mux (eq (extract v_6200 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6200 1 9)) (concat (mux (eq (extract v_6209 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6209 1 9)) (concat (mux (eq (extract v_6218 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6218 1 9)) (concat (mux (eq (extract v_6227 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6227 1 9)) (concat (mux (eq (extract v_6236 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6236 1 9)) (mux (eq (extract v_6245 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6245 1 9)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3151 : Mem) (v_3152 : reg (bv 128)) => do
      v_10185 <- getRegister v_3152;
      v_10188 <- evaluateAddress v_3151;
      v_10189 <- load v_10188 16;
      v_10192 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 0 8)) (concat (expression.bv_nat 1 0) (extract v_10189 0 8)));
      v_10201 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 8 16)) (concat (expression.bv_nat 1 0) (extract v_10189 8 16)));
      v_10210 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 16 24)) (concat (expression.bv_nat 1 0) (extract v_10189 16 24)));
      v_10219 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 24 32)) (concat (expression.bv_nat 1 0) (extract v_10189 24 32)));
      v_10228 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 32 40)) (concat (expression.bv_nat 1 0) (extract v_10189 32 40)));
      v_10237 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 40 48)) (concat (expression.bv_nat 1 0) (extract v_10189 40 48)));
      v_10246 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 48 56)) (concat (expression.bv_nat 1 0) (extract v_10189 48 56)));
      v_10255 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 56 64)) (concat (expression.bv_nat 1 0) (extract v_10189 56 64)));
      v_10264 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 64 72)) (concat (expression.bv_nat 1 0) (extract v_10189 64 72)));
      v_10273 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 72 80)) (concat (expression.bv_nat 1 0) (extract v_10189 72 80)));
      v_10282 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 80 88)) (concat (expression.bv_nat 1 0) (extract v_10189 80 88)));
      v_10291 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 88 96)) (concat (expression.bv_nat 1 0) (extract v_10189 88 96)));
      v_10300 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 96 104)) (concat (expression.bv_nat 1 0) (extract v_10189 96 104)));
      v_10309 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 104 112)) (concat (expression.bv_nat 1 0) (extract v_10189 104 112)));
      v_10318 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 112 120)) (concat (expression.bv_nat 1 0) (extract v_10189 112 120)));
      v_10327 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10185 120 128)) (concat (expression.bv_nat 1 0) (extract v_10189 120 128)));
      setRegister (lhs.of_reg v_3152) (concat (mux (eq (extract v_10192 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10192 1 9)) (concat (mux (eq (extract v_10201 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10201 1 9)) (concat (mux (eq (extract v_10210 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10210 1 9)) (concat (mux (eq (extract v_10219 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10219 1 9)) (concat (mux (eq (extract v_10228 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10228 1 9)) (concat (mux (eq (extract v_10237 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10237 1 9)) (concat (mux (eq (extract v_10246 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10246 1 9)) (concat (mux (eq (extract v_10255 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10255 1 9)) (concat (mux (eq (extract v_10264 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10264 1 9)) (concat (mux (eq (extract v_10273 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10273 1 9)) (concat (mux (eq (extract v_10282 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10282 1 9)) (concat (mux (eq (extract v_10291 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10291 1 9)) (concat (mux (eq (extract v_10300 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10300 1 9)) (concat (mux (eq (extract v_10309 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10309 1 9)) (concat (mux (eq (extract v_10318 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10318 1 9)) (mux (eq (extract v_10327 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10327 1 9)))))))))))))))));
      pure ()
    pat_end
