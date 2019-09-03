def paddusb1 : instruction :=
  definst "paddusb" $ do
    pattern fun (v_3168 : reg (bv 128)) (v_3169 : reg (bv 128)) => do
      v_6087 <- getRegister v_3169;
      v_6090 <- getRegister v_3168;
      v_6093 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 0 8)) (concat (expression.bv_nat 1 0) (extract v_6090 0 8)));
      v_6102 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 8 16)) (concat (expression.bv_nat 1 0) (extract v_6090 8 16)));
      v_6111 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 16 24)) (concat (expression.bv_nat 1 0) (extract v_6090 16 24)));
      v_6120 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 24 32)) (concat (expression.bv_nat 1 0) (extract v_6090 24 32)));
      v_6129 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 32 40)) (concat (expression.bv_nat 1 0) (extract v_6090 32 40)));
      v_6138 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 40 48)) (concat (expression.bv_nat 1 0) (extract v_6090 40 48)));
      v_6147 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 48 56)) (concat (expression.bv_nat 1 0) (extract v_6090 48 56)));
      v_6156 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 56 64)) (concat (expression.bv_nat 1 0) (extract v_6090 56 64)));
      v_6165 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 64 72)) (concat (expression.bv_nat 1 0) (extract v_6090 64 72)));
      v_6174 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 72 80)) (concat (expression.bv_nat 1 0) (extract v_6090 72 80)));
      v_6183 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 80 88)) (concat (expression.bv_nat 1 0) (extract v_6090 80 88)));
      v_6192 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 88 96)) (concat (expression.bv_nat 1 0) (extract v_6090 88 96)));
      v_6201 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 96 104)) (concat (expression.bv_nat 1 0) (extract v_6090 96 104)));
      v_6210 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 104 112)) (concat (expression.bv_nat 1 0) (extract v_6090 104 112)));
      v_6219 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 112 120)) (concat (expression.bv_nat 1 0) (extract v_6090 112 120)));
      v_6228 <- eval (add (concat (expression.bv_nat 1 0) (extract v_6087 120 128)) (concat (expression.bv_nat 1 0) (extract v_6090 120 128)));
      setRegister (lhs.of_reg v_3169) (concat (mux (eq (extract v_6093 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6093 1 9)) (concat (mux (eq (extract v_6102 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6102 1 9)) (concat (mux (eq (extract v_6111 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6111 1 9)) (concat (mux (eq (extract v_6120 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6120 1 9)) (concat (mux (eq (extract v_6129 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6129 1 9)) (concat (mux (eq (extract v_6138 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6138 1 9)) (concat (mux (eq (extract v_6147 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6147 1 9)) (concat (mux (eq (extract v_6156 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6156 1 9)) (concat (mux (eq (extract v_6165 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6165 1 9)) (concat (mux (eq (extract v_6174 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6174 1 9)) (concat (mux (eq (extract v_6183 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6183 1 9)) (concat (mux (eq (extract v_6192 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6192 1 9)) (concat (mux (eq (extract v_6201 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6201 1 9)) (concat (mux (eq (extract v_6210 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6210 1 9)) (concat (mux (eq (extract v_6219 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6219 1 9)) (mux (eq (extract v_6228 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_6228 1 9)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3164 : Mem) (v_3165 : reg (bv 128)) => do
      v_10156 <- getRegister v_3165;
      v_10159 <- evaluateAddress v_3164;
      v_10160 <- load v_10159 16;
      v_10163 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 0 8)) (concat (expression.bv_nat 1 0) (extract v_10160 0 8)));
      v_10172 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 8 16)) (concat (expression.bv_nat 1 0) (extract v_10160 8 16)));
      v_10181 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 16 24)) (concat (expression.bv_nat 1 0) (extract v_10160 16 24)));
      v_10190 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 24 32)) (concat (expression.bv_nat 1 0) (extract v_10160 24 32)));
      v_10199 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 32 40)) (concat (expression.bv_nat 1 0) (extract v_10160 32 40)));
      v_10208 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 40 48)) (concat (expression.bv_nat 1 0) (extract v_10160 40 48)));
      v_10217 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 48 56)) (concat (expression.bv_nat 1 0) (extract v_10160 48 56)));
      v_10226 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 56 64)) (concat (expression.bv_nat 1 0) (extract v_10160 56 64)));
      v_10235 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 64 72)) (concat (expression.bv_nat 1 0) (extract v_10160 64 72)));
      v_10244 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 72 80)) (concat (expression.bv_nat 1 0) (extract v_10160 72 80)));
      v_10253 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 80 88)) (concat (expression.bv_nat 1 0) (extract v_10160 80 88)));
      v_10262 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 88 96)) (concat (expression.bv_nat 1 0) (extract v_10160 88 96)));
      v_10271 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 96 104)) (concat (expression.bv_nat 1 0) (extract v_10160 96 104)));
      v_10280 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 104 112)) (concat (expression.bv_nat 1 0) (extract v_10160 104 112)));
      v_10289 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 112 120)) (concat (expression.bv_nat 1 0) (extract v_10160 112 120)));
      v_10298 <- eval (add (concat (expression.bv_nat 1 0) (extract v_10156 120 128)) (concat (expression.bv_nat 1 0) (extract v_10160 120 128)));
      setRegister (lhs.of_reg v_3165) (concat (mux (eq (extract v_10163 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10163 1 9)) (concat (mux (eq (extract v_10172 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10172 1 9)) (concat (mux (eq (extract v_10181 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10181 1 9)) (concat (mux (eq (extract v_10190 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10190 1 9)) (concat (mux (eq (extract v_10199 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10199 1 9)) (concat (mux (eq (extract v_10208 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10208 1 9)) (concat (mux (eq (extract v_10217 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10217 1 9)) (concat (mux (eq (extract v_10226 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10226 1 9)) (concat (mux (eq (extract v_10235 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10235 1 9)) (concat (mux (eq (extract v_10244 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10244 1 9)) (concat (mux (eq (extract v_10253 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10253 1 9)) (concat (mux (eq (extract v_10262 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10262 1 9)) (concat (mux (eq (extract v_10271 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10271 1 9)) (concat (mux (eq (extract v_10280 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10280 1 9)) (concat (mux (eq (extract v_10289 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10289 1 9)) (mux (eq (extract v_10298 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 8 255) (extract v_10298 1 9)))))))))))))))));
      pure ()
    pat_end
