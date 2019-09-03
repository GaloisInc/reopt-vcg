def vpsubw1 : instruction :=
  definst "vpsubw" $ do
    pattern fun (v_2540 : reg (bv 128)) (v_2541 : reg (bv 128)) (v_2542 : reg (bv 128)) => do
      v_6005 <- getRegister v_2541;
      v_6007 <- getRegister v_2540;
      setRegister (lhs.of_reg v_2542) (concat (sub (extract v_6005 0 16) (extract v_6007 0 16)) (concat (sub (extract v_6005 16 32) (extract v_6007 16 32)) (concat (sub (extract v_6005 32 48) (extract v_6007 32 48)) (concat (sub (extract v_6005 48 64) (extract v_6007 48 64)) (concat (sub (extract v_6005 64 80) (extract v_6007 64 80)) (concat (sub (extract v_6005 80 96) (extract v_6007 80 96)) (concat (sub (extract v_6005 96 112) (extract v_6007 96 112)) (sub (extract v_6005 112 128) (extract v_6007 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2550 : reg (bv 256)) (v_2551 : reg (bv 256)) (v_2552 : reg (bv 256)) => do
      v_6044 <- getRegister v_2551;
      v_6046 <- getRegister v_2550;
      setRegister (lhs.of_reg v_2552) (concat (sub (extract v_6044 0 16) (extract v_6046 0 16)) (concat (sub (extract v_6044 16 32) (extract v_6046 16 32)) (concat (sub (extract v_6044 32 48) (extract v_6046 32 48)) (concat (sub (extract v_6044 48 64) (extract v_6046 48 64)) (concat (sub (extract v_6044 64 80) (extract v_6046 64 80)) (concat (sub (extract v_6044 80 96) (extract v_6046 80 96)) (concat (sub (extract v_6044 96 112) (extract v_6046 96 112)) (concat (sub (extract v_6044 112 128) (extract v_6046 112 128)) (concat (sub (extract v_6044 128 144) (extract v_6046 128 144)) (concat (sub (extract v_6044 144 160) (extract v_6046 144 160)) (concat (sub (extract v_6044 160 176) (extract v_6046 160 176)) (concat (sub (extract v_6044 176 192) (extract v_6046 176 192)) (concat (sub (extract v_6044 192 208) (extract v_6046 192 208)) (concat (sub (extract v_6044 208 224) (extract v_6046 208 224)) (concat (sub (extract v_6044 224 240) (extract v_6046 224 240)) (sub (extract v_6044 240 256) (extract v_6046 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2534 : Mem) (v_2535 : reg (bv 128)) (v_2536 : reg (bv 128)) => do
      v_12350 <- getRegister v_2535;
      v_12352 <- evaluateAddress v_2534;
      v_12353 <- load v_12352 16;
      setRegister (lhs.of_reg v_2536) (concat (sub (extract v_12350 0 16) (extract v_12353 0 16)) (concat (sub (extract v_12350 16 32) (extract v_12353 16 32)) (concat (sub (extract v_12350 32 48) (extract v_12353 32 48)) (concat (sub (extract v_12350 48 64) (extract v_12353 48 64)) (concat (sub (extract v_12350 64 80) (extract v_12353 64 80)) (concat (sub (extract v_12350 80 96) (extract v_12353 80 96)) (concat (sub (extract v_12350 96 112) (extract v_12353 96 112)) (sub (extract v_12350 112 128) (extract v_12353 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2545 : Mem) (v_2546 : reg (bv 256)) (v_2547 : reg (bv 256)) => do
      v_12385 <- getRegister v_2546;
      v_12387 <- evaluateAddress v_2545;
      v_12388 <- load v_12387 32;
      setRegister (lhs.of_reg v_2547) (concat (sub (extract v_12385 0 16) (extract v_12388 0 16)) (concat (sub (extract v_12385 16 32) (extract v_12388 16 32)) (concat (sub (extract v_12385 32 48) (extract v_12388 32 48)) (concat (sub (extract v_12385 48 64) (extract v_12388 48 64)) (concat (sub (extract v_12385 64 80) (extract v_12388 64 80)) (concat (sub (extract v_12385 80 96) (extract v_12388 80 96)) (concat (sub (extract v_12385 96 112) (extract v_12388 96 112)) (concat (sub (extract v_12385 112 128) (extract v_12388 112 128)) (concat (sub (extract v_12385 128 144) (extract v_12388 128 144)) (concat (sub (extract v_12385 144 160) (extract v_12388 144 160)) (concat (sub (extract v_12385 160 176) (extract v_12388 160 176)) (concat (sub (extract v_12385 176 192) (extract v_12388 176 192)) (concat (sub (extract v_12385 192 208) (extract v_12388 192 208)) (concat (sub (extract v_12385 208 224) (extract v_12388 208 224)) (concat (sub (extract v_12385 224 240) (extract v_12388 224 240)) (sub (extract v_12385 240 256) (extract v_12388 240 256)))))))))))))))));
      pure ()
    pat_end
