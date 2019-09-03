def vpsubw1 : instruction :=
  definst "vpsubw" $ do
    pattern fun (v_2550 : reg (bv 128)) (v_2551 : reg (bv 128)) (v_2552 : reg (bv 128)) => do
      v_5874 <- getRegister v_2551;
      v_5876 <- getRegister v_2550;
      setRegister (lhs.of_reg v_2552) (concat (sub (extract v_5874 0 16) (extract v_5876 0 16)) (concat (sub (extract v_5874 16 32) (extract v_5876 16 32)) (concat (sub (extract v_5874 32 48) (extract v_5876 32 48)) (concat (sub (extract v_5874 48 64) (extract v_5876 48 64)) (concat (sub (extract v_5874 64 80) (extract v_5876 64 80)) (concat (sub (extract v_5874 80 96) (extract v_5876 80 96)) (concat (sub (extract v_5874 96 112) (extract v_5876 96 112)) (sub (extract v_5874 112 128) (extract v_5876 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2561 : reg (bv 256)) (v_2562 : reg (bv 256)) (v_2563 : reg (bv 256)) => do
      v_5913 <- getRegister v_2562;
      v_5915 <- getRegister v_2561;
      setRegister (lhs.of_reg v_2563) (concat (sub (extract v_5913 0 16) (extract v_5915 0 16)) (concat (sub (extract v_5913 16 32) (extract v_5915 16 32)) (concat (sub (extract v_5913 32 48) (extract v_5915 32 48)) (concat (sub (extract v_5913 48 64) (extract v_5915 48 64)) (concat (sub (extract v_5913 64 80) (extract v_5915 64 80)) (concat (sub (extract v_5913 80 96) (extract v_5915 80 96)) (concat (sub (extract v_5913 96 112) (extract v_5915 96 112)) (concat (sub (extract v_5913 112 128) (extract v_5915 112 128)) (concat (sub (extract v_5913 128 144) (extract v_5915 128 144)) (concat (sub (extract v_5913 144 160) (extract v_5915 144 160)) (concat (sub (extract v_5913 160 176) (extract v_5915 160 176)) (concat (sub (extract v_5913 176 192) (extract v_5915 176 192)) (concat (sub (extract v_5913 192 208) (extract v_5915 192 208)) (concat (sub (extract v_5913 208 224) (extract v_5915 208 224)) (concat (sub (extract v_5913 224 240) (extract v_5915 224 240)) (sub (extract v_5913 240 256) (extract v_5915 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2545 : Mem) (v_2546 : reg (bv 128)) (v_2547 : reg (bv 128)) => do
      v_12351 <- getRegister v_2546;
      v_12353 <- evaluateAddress v_2545;
      v_12354 <- load v_12353 16;
      setRegister (lhs.of_reg v_2547) (concat (sub (extract v_12351 0 16) (extract v_12354 0 16)) (concat (sub (extract v_12351 16 32) (extract v_12354 16 32)) (concat (sub (extract v_12351 32 48) (extract v_12354 32 48)) (concat (sub (extract v_12351 48 64) (extract v_12354 48 64)) (concat (sub (extract v_12351 64 80) (extract v_12354 64 80)) (concat (sub (extract v_12351 80 96) (extract v_12354 80 96)) (concat (sub (extract v_12351 96 112) (extract v_12354 96 112)) (sub (extract v_12351 112 128) (extract v_12354 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2556 : Mem) (v_2557 : reg (bv 256)) (v_2558 : reg (bv 256)) => do
      v_12386 <- getRegister v_2557;
      v_12388 <- evaluateAddress v_2556;
      v_12389 <- load v_12388 32;
      setRegister (lhs.of_reg v_2558) (concat (sub (extract v_12386 0 16) (extract v_12389 0 16)) (concat (sub (extract v_12386 16 32) (extract v_12389 16 32)) (concat (sub (extract v_12386 32 48) (extract v_12389 32 48)) (concat (sub (extract v_12386 48 64) (extract v_12389 48 64)) (concat (sub (extract v_12386 64 80) (extract v_12389 64 80)) (concat (sub (extract v_12386 80 96) (extract v_12389 80 96)) (concat (sub (extract v_12386 96 112) (extract v_12389 96 112)) (concat (sub (extract v_12386 112 128) (extract v_12389 112 128)) (concat (sub (extract v_12386 128 144) (extract v_12389 128 144)) (concat (sub (extract v_12386 144 160) (extract v_12389 144 160)) (concat (sub (extract v_12386 160 176) (extract v_12389 160 176)) (concat (sub (extract v_12386 176 192) (extract v_12389 176 192)) (concat (sub (extract v_12386 192 208) (extract v_12389 192 208)) (concat (sub (extract v_12386 208 224) (extract v_12389 208 224)) (concat (sub (extract v_12386 224 240) (extract v_12389 224 240)) (sub (extract v_12386 240 256) (extract v_12389 240 256)))))))))))))))));
      pure ()
    pat_end
