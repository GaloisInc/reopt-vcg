def vpmaddubsw1 : instruction :=
  definst "vpmaddubsw" $ do
    pattern fun (v_3433 : reg (bv 128)) (v_3434 : reg (bv 128)) (v_3435 : reg (bv 128)) => do
      v_9718 <- getRegister v_3433;
      v_9721 <- getRegister v_3434;
      v_9732 <- eval (add (sext (mul (sext (extract v_9718 8 16) 16) (concat (expression.bv_nat 8 0) (extract v_9721 8 16))) 32) (sext (mul (sext (extract v_9718 0 8) 16) (concat (expression.bv_nat 8 0) (extract v_9721 0 8))) 32));
      v_9750 <- eval (add (sext (mul (sext (extract v_9718 24 32) 16) (concat (expression.bv_nat 8 0) (extract v_9721 24 32))) 32) (sext (mul (sext (extract v_9718 16 24) 16) (concat (expression.bv_nat 8 0) (extract v_9721 16 24))) 32));
      v_9768 <- eval (add (sext (mul (sext (extract v_9718 40 48) 16) (concat (expression.bv_nat 8 0) (extract v_9721 40 48))) 32) (sext (mul (sext (extract v_9718 32 40) 16) (concat (expression.bv_nat 8 0) (extract v_9721 32 40))) 32));
      v_9786 <- eval (add (sext (mul (sext (extract v_9718 56 64) 16) (concat (expression.bv_nat 8 0) (extract v_9721 56 64))) 32) (sext (mul (sext (extract v_9718 48 56) 16) (concat (expression.bv_nat 8 0) (extract v_9721 48 56))) 32));
      v_9804 <- eval (add (sext (mul (sext (extract v_9718 72 80) 16) (concat (expression.bv_nat 8 0) (extract v_9721 72 80))) 32) (sext (mul (sext (extract v_9718 64 72) 16) (concat (expression.bv_nat 8 0) (extract v_9721 64 72))) 32));
      v_9822 <- eval (add (sext (mul (sext (extract v_9718 88 96) 16) (concat (expression.bv_nat 8 0) (extract v_9721 88 96))) 32) (sext (mul (sext (extract v_9718 80 88) 16) (concat (expression.bv_nat 8 0) (extract v_9721 80 88))) 32));
      v_9840 <- eval (add (sext (mul (sext (extract v_9718 104 112) 16) (concat (expression.bv_nat 8 0) (extract v_9721 104 112))) 32) (sext (mul (sext (extract v_9718 96 104) 16) (concat (expression.bv_nat 8 0) (extract v_9721 96 104))) 32));
      v_9858 <- eval (add (sext (mul (sext (extract v_9718 120 128) 16) (concat (expression.bv_nat 8 0) (extract v_9721 120 128))) 32) (sext (mul (sext (extract v_9718 112 120) 16) (concat (expression.bv_nat 8 0) (extract v_9721 112 120))) 32));
      setRegister (lhs.of_reg v_3435) (concat (mux (sgt v_9732 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9732 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9732 16 32))) (concat (mux (sgt v_9750 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9750 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9750 16 32))) (concat (mux (sgt v_9768 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9768 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9768 16 32))) (concat (mux (sgt v_9786 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9786 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9786 16 32))) (concat (mux (sgt v_9804 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9804 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9804 16 32))) (concat (mux (sgt v_9822 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9822 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9822 16 32))) (concat (mux (sgt v_9840 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9840 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9840 16 32))) (mux (sgt v_9858 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9858 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9858 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3444 : reg (bv 256)) (v_3445 : reg (bv 256)) (v_3446 : reg (bv 256)) => do
      v_9877 <- getRegister v_3444;
      v_9880 <- getRegister v_3445;
      v_9891 <- eval (add (sext (mul (sext (extract v_9877 8 16) 16) (concat (expression.bv_nat 8 0) (extract v_9880 8 16))) 32) (sext (mul (sext (extract v_9877 0 8) 16) (concat (expression.bv_nat 8 0) (extract v_9880 0 8))) 32));
      v_9909 <- eval (add (sext (mul (sext (extract v_9877 24 32) 16) (concat (expression.bv_nat 8 0) (extract v_9880 24 32))) 32) (sext (mul (sext (extract v_9877 16 24) 16) (concat (expression.bv_nat 8 0) (extract v_9880 16 24))) 32));
      v_9927 <- eval (add (sext (mul (sext (extract v_9877 40 48) 16) (concat (expression.bv_nat 8 0) (extract v_9880 40 48))) 32) (sext (mul (sext (extract v_9877 32 40) 16) (concat (expression.bv_nat 8 0) (extract v_9880 32 40))) 32));
      v_9945 <- eval (add (sext (mul (sext (extract v_9877 56 64) 16) (concat (expression.bv_nat 8 0) (extract v_9880 56 64))) 32) (sext (mul (sext (extract v_9877 48 56) 16) (concat (expression.bv_nat 8 0) (extract v_9880 48 56))) 32));
      v_9963 <- eval (add (sext (mul (sext (extract v_9877 72 80) 16) (concat (expression.bv_nat 8 0) (extract v_9880 72 80))) 32) (sext (mul (sext (extract v_9877 64 72) 16) (concat (expression.bv_nat 8 0) (extract v_9880 64 72))) 32));
      v_9981 <- eval (add (sext (mul (sext (extract v_9877 88 96) 16) (concat (expression.bv_nat 8 0) (extract v_9880 88 96))) 32) (sext (mul (sext (extract v_9877 80 88) 16) (concat (expression.bv_nat 8 0) (extract v_9880 80 88))) 32));
      v_9999 <- eval (add (sext (mul (sext (extract v_9877 104 112) 16) (concat (expression.bv_nat 8 0) (extract v_9880 104 112))) 32) (sext (mul (sext (extract v_9877 96 104) 16) (concat (expression.bv_nat 8 0) (extract v_9880 96 104))) 32));
      v_10017 <- eval (add (sext (mul (sext (extract v_9877 120 128) 16) (concat (expression.bv_nat 8 0) (extract v_9880 120 128))) 32) (sext (mul (sext (extract v_9877 112 120) 16) (concat (expression.bv_nat 8 0) (extract v_9880 112 120))) 32));
      v_10035 <- eval (add (sext (mul (sext (extract v_9877 136 144) 16) (concat (expression.bv_nat 8 0) (extract v_9880 136 144))) 32) (sext (mul (sext (extract v_9877 128 136) 16) (concat (expression.bv_nat 8 0) (extract v_9880 128 136))) 32));
      v_10053 <- eval (add (sext (mul (sext (extract v_9877 152 160) 16) (concat (expression.bv_nat 8 0) (extract v_9880 152 160))) 32) (sext (mul (sext (extract v_9877 144 152) 16) (concat (expression.bv_nat 8 0) (extract v_9880 144 152))) 32));
      v_10071 <- eval (add (sext (mul (sext (extract v_9877 168 176) 16) (concat (expression.bv_nat 8 0) (extract v_9880 168 176))) 32) (sext (mul (sext (extract v_9877 160 168) 16) (concat (expression.bv_nat 8 0) (extract v_9880 160 168))) 32));
      v_10089 <- eval (add (sext (mul (sext (extract v_9877 184 192) 16) (concat (expression.bv_nat 8 0) (extract v_9880 184 192))) 32) (sext (mul (sext (extract v_9877 176 184) 16) (concat (expression.bv_nat 8 0) (extract v_9880 176 184))) 32));
      v_10107 <- eval (add (sext (mul (sext (extract v_9877 200 208) 16) (concat (expression.bv_nat 8 0) (extract v_9880 200 208))) 32) (sext (mul (sext (extract v_9877 192 200) 16) (concat (expression.bv_nat 8 0) (extract v_9880 192 200))) 32));
      v_10125 <- eval (add (sext (mul (sext (extract v_9877 216 224) 16) (concat (expression.bv_nat 8 0) (extract v_9880 216 224))) 32) (sext (mul (sext (extract v_9877 208 216) 16) (concat (expression.bv_nat 8 0) (extract v_9880 208 216))) 32));
      v_10143 <- eval (add (sext (mul (sext (extract v_9877 232 240) 16) (concat (expression.bv_nat 8 0) (extract v_9880 232 240))) 32) (sext (mul (sext (extract v_9877 224 232) 16) (concat (expression.bv_nat 8 0) (extract v_9880 224 232))) 32));
      v_10161 <- eval (add (sext (mul (sext (extract v_9877 248 256) 16) (concat (expression.bv_nat 8 0) (extract v_9880 248 256))) 32) (sext (mul (sext (extract v_9877 240 248) 16) (concat (expression.bv_nat 8 0) (extract v_9880 240 248))) 32));
      setRegister (lhs.of_reg v_3446) (concat (mux (sgt v_9891 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9891 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9891 16 32))) (concat (mux (sgt v_9909 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9909 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9909 16 32))) (concat (mux (sgt v_9927 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9927 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9927 16 32))) (concat (mux (sgt v_9945 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9945 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9945 16 32))) (concat (mux (sgt v_9963 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9963 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9963 16 32))) (concat (mux (sgt v_9981 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9981 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9981 16 32))) (concat (mux (sgt v_9999 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9999 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9999 16 32))) (concat (mux (sgt v_10017 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10017 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10017 16 32))) (concat (mux (sgt v_10035 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10035 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10035 16 32))) (concat (mux (sgt v_10053 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10053 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10053 16 32))) (concat (mux (sgt v_10071 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10071 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10071 16 32))) (concat (mux (sgt v_10089 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10089 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10089 16 32))) (concat (mux (sgt v_10107 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10107 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10107 16 32))) (concat (mux (sgt v_10125 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10125 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10125 16 32))) (concat (mux (sgt v_10143 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10143 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10143 16 32))) (mux (sgt v_10161 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10161 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10161 16 32))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3428 : Mem) (v_3429 : reg (bv 128)) (v_3430 : reg (bv 128)) => do
      v_18067 <- evaluateAddress v_3428;
      v_18068 <- load v_18067 16;
      v_18071 <- getRegister v_3429;
      v_18082 <- eval (add (sext (mul (sext (extract v_18068 8 16) 16) (concat (expression.bv_nat 8 0) (extract v_18071 8 16))) 32) (sext (mul (sext (extract v_18068 0 8) 16) (concat (expression.bv_nat 8 0) (extract v_18071 0 8))) 32));
      v_18100 <- eval (add (sext (mul (sext (extract v_18068 24 32) 16) (concat (expression.bv_nat 8 0) (extract v_18071 24 32))) 32) (sext (mul (sext (extract v_18068 16 24) 16) (concat (expression.bv_nat 8 0) (extract v_18071 16 24))) 32));
      v_18118 <- eval (add (sext (mul (sext (extract v_18068 40 48) 16) (concat (expression.bv_nat 8 0) (extract v_18071 40 48))) 32) (sext (mul (sext (extract v_18068 32 40) 16) (concat (expression.bv_nat 8 0) (extract v_18071 32 40))) 32));
      v_18136 <- eval (add (sext (mul (sext (extract v_18068 56 64) 16) (concat (expression.bv_nat 8 0) (extract v_18071 56 64))) 32) (sext (mul (sext (extract v_18068 48 56) 16) (concat (expression.bv_nat 8 0) (extract v_18071 48 56))) 32));
      v_18154 <- eval (add (sext (mul (sext (extract v_18068 72 80) 16) (concat (expression.bv_nat 8 0) (extract v_18071 72 80))) 32) (sext (mul (sext (extract v_18068 64 72) 16) (concat (expression.bv_nat 8 0) (extract v_18071 64 72))) 32));
      v_18172 <- eval (add (sext (mul (sext (extract v_18068 88 96) 16) (concat (expression.bv_nat 8 0) (extract v_18071 88 96))) 32) (sext (mul (sext (extract v_18068 80 88) 16) (concat (expression.bv_nat 8 0) (extract v_18071 80 88))) 32));
      v_18190 <- eval (add (sext (mul (sext (extract v_18068 104 112) 16) (concat (expression.bv_nat 8 0) (extract v_18071 104 112))) 32) (sext (mul (sext (extract v_18068 96 104) 16) (concat (expression.bv_nat 8 0) (extract v_18071 96 104))) 32));
      v_18208 <- eval (add (sext (mul (sext (extract v_18068 120 128) 16) (concat (expression.bv_nat 8 0) (extract v_18071 120 128))) 32) (sext (mul (sext (extract v_18068 112 120) 16) (concat (expression.bv_nat 8 0) (extract v_18071 112 120))) 32));
      setRegister (lhs.of_reg v_3430) (concat (mux (sgt v_18082 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18082 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18082 16 32))) (concat (mux (sgt v_18100 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18100 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18100 16 32))) (concat (mux (sgt v_18118 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18118 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18118 16 32))) (concat (mux (sgt v_18136 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18136 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18136 16 32))) (concat (mux (sgt v_18154 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18154 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18154 16 32))) (concat (mux (sgt v_18172 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18172 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18172 16 32))) (concat (mux (sgt v_18190 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18190 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18190 16 32))) (mux (sgt v_18208 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18208 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18208 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3439 : Mem) (v_3440 : reg (bv 256)) (v_3441 : reg (bv 256)) => do
      v_18222 <- evaluateAddress v_3439;
      v_18223 <- load v_18222 32;
      v_18226 <- getRegister v_3440;
      v_18237 <- eval (add (sext (mul (sext (extract v_18223 8 16) 16) (concat (expression.bv_nat 8 0) (extract v_18226 8 16))) 32) (sext (mul (sext (extract v_18223 0 8) 16) (concat (expression.bv_nat 8 0) (extract v_18226 0 8))) 32));
      v_18255 <- eval (add (sext (mul (sext (extract v_18223 24 32) 16) (concat (expression.bv_nat 8 0) (extract v_18226 24 32))) 32) (sext (mul (sext (extract v_18223 16 24) 16) (concat (expression.bv_nat 8 0) (extract v_18226 16 24))) 32));
      v_18273 <- eval (add (sext (mul (sext (extract v_18223 40 48) 16) (concat (expression.bv_nat 8 0) (extract v_18226 40 48))) 32) (sext (mul (sext (extract v_18223 32 40) 16) (concat (expression.bv_nat 8 0) (extract v_18226 32 40))) 32));
      v_18291 <- eval (add (sext (mul (sext (extract v_18223 56 64) 16) (concat (expression.bv_nat 8 0) (extract v_18226 56 64))) 32) (sext (mul (sext (extract v_18223 48 56) 16) (concat (expression.bv_nat 8 0) (extract v_18226 48 56))) 32));
      v_18309 <- eval (add (sext (mul (sext (extract v_18223 72 80) 16) (concat (expression.bv_nat 8 0) (extract v_18226 72 80))) 32) (sext (mul (sext (extract v_18223 64 72) 16) (concat (expression.bv_nat 8 0) (extract v_18226 64 72))) 32));
      v_18327 <- eval (add (sext (mul (sext (extract v_18223 88 96) 16) (concat (expression.bv_nat 8 0) (extract v_18226 88 96))) 32) (sext (mul (sext (extract v_18223 80 88) 16) (concat (expression.bv_nat 8 0) (extract v_18226 80 88))) 32));
      v_18345 <- eval (add (sext (mul (sext (extract v_18223 104 112) 16) (concat (expression.bv_nat 8 0) (extract v_18226 104 112))) 32) (sext (mul (sext (extract v_18223 96 104) 16) (concat (expression.bv_nat 8 0) (extract v_18226 96 104))) 32));
      v_18363 <- eval (add (sext (mul (sext (extract v_18223 120 128) 16) (concat (expression.bv_nat 8 0) (extract v_18226 120 128))) 32) (sext (mul (sext (extract v_18223 112 120) 16) (concat (expression.bv_nat 8 0) (extract v_18226 112 120))) 32));
      v_18381 <- eval (add (sext (mul (sext (extract v_18223 136 144) 16) (concat (expression.bv_nat 8 0) (extract v_18226 136 144))) 32) (sext (mul (sext (extract v_18223 128 136) 16) (concat (expression.bv_nat 8 0) (extract v_18226 128 136))) 32));
      v_18399 <- eval (add (sext (mul (sext (extract v_18223 152 160) 16) (concat (expression.bv_nat 8 0) (extract v_18226 152 160))) 32) (sext (mul (sext (extract v_18223 144 152) 16) (concat (expression.bv_nat 8 0) (extract v_18226 144 152))) 32));
      v_18417 <- eval (add (sext (mul (sext (extract v_18223 168 176) 16) (concat (expression.bv_nat 8 0) (extract v_18226 168 176))) 32) (sext (mul (sext (extract v_18223 160 168) 16) (concat (expression.bv_nat 8 0) (extract v_18226 160 168))) 32));
      v_18435 <- eval (add (sext (mul (sext (extract v_18223 184 192) 16) (concat (expression.bv_nat 8 0) (extract v_18226 184 192))) 32) (sext (mul (sext (extract v_18223 176 184) 16) (concat (expression.bv_nat 8 0) (extract v_18226 176 184))) 32));
      v_18453 <- eval (add (sext (mul (sext (extract v_18223 200 208) 16) (concat (expression.bv_nat 8 0) (extract v_18226 200 208))) 32) (sext (mul (sext (extract v_18223 192 200) 16) (concat (expression.bv_nat 8 0) (extract v_18226 192 200))) 32));
      v_18471 <- eval (add (sext (mul (sext (extract v_18223 216 224) 16) (concat (expression.bv_nat 8 0) (extract v_18226 216 224))) 32) (sext (mul (sext (extract v_18223 208 216) 16) (concat (expression.bv_nat 8 0) (extract v_18226 208 216))) 32));
      v_18489 <- eval (add (sext (mul (sext (extract v_18223 232 240) 16) (concat (expression.bv_nat 8 0) (extract v_18226 232 240))) 32) (sext (mul (sext (extract v_18223 224 232) 16) (concat (expression.bv_nat 8 0) (extract v_18226 224 232))) 32));
      v_18507 <- eval (add (sext (mul (sext (extract v_18223 248 256) 16) (concat (expression.bv_nat 8 0) (extract v_18226 248 256))) 32) (sext (mul (sext (extract v_18223 240 248) 16) (concat (expression.bv_nat 8 0) (extract v_18226 240 248))) 32));
      setRegister (lhs.of_reg v_3441) (concat (mux (sgt v_18237 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18237 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18237 16 32))) (concat (mux (sgt v_18255 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18255 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18255 16 32))) (concat (mux (sgt v_18273 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18273 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18273 16 32))) (concat (mux (sgt v_18291 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18291 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18291 16 32))) (concat (mux (sgt v_18309 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18309 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18309 16 32))) (concat (mux (sgt v_18327 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18327 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18327 16 32))) (concat (mux (sgt v_18345 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18345 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18345 16 32))) (concat (mux (sgt v_18363 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18363 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18363 16 32))) (concat (mux (sgt v_18381 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18381 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18381 16 32))) (concat (mux (sgt v_18399 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18399 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18399 16 32))) (concat (mux (sgt v_18417 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18417 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18417 16 32))) (concat (mux (sgt v_18435 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18435 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18435 16 32))) (concat (mux (sgt v_18453 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18453 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18453 16 32))) (concat (mux (sgt v_18471 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18471 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18471 16 32))) (concat (mux (sgt v_18489 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18489 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18489 16 32))) (mux (sgt v_18507 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18507 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18507 16 32))))))))))))))))));
      pure ()
    pat_end
