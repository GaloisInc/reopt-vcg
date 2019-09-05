def vpsubw1 : instruction :=
  definst "vpsubw" $ do
    pattern fun (v_2604 : reg (bv 128)) (v_2605 : reg (bv 128)) (v_2606 : reg (bv 128)) => do
      v_5925 <- getRegister v_2605;
      v_5927 <- getRegister v_2604;
      setRegister (lhs.of_reg v_2606) (concat (sub (extract v_5925 0 16) (extract v_5927 0 16)) (concat (sub (extract v_5925 16 32) (extract v_5927 16 32)) (concat (sub (extract v_5925 32 48) (extract v_5927 32 48)) (concat (sub (extract v_5925 48 64) (extract v_5927 48 64)) (concat (sub (extract v_5925 64 80) (extract v_5927 64 80)) (concat (sub (extract v_5925 80 96) (extract v_5927 80 96)) (concat (sub (extract v_5925 96 112) (extract v_5927 96 112)) (sub (extract v_5925 112 128) (extract v_5927 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2615 : reg (bv 256)) (v_2616 : reg (bv 256)) (v_2617 : reg (bv 256)) => do
      v_5964 <- getRegister v_2616;
      v_5966 <- getRegister v_2615;
      setRegister (lhs.of_reg v_2617) (concat (sub (extract v_5964 0 16) (extract v_5966 0 16)) (concat (sub (extract v_5964 16 32) (extract v_5966 16 32)) (concat (sub (extract v_5964 32 48) (extract v_5966 32 48)) (concat (sub (extract v_5964 48 64) (extract v_5966 48 64)) (concat (sub (extract v_5964 64 80) (extract v_5966 64 80)) (concat (sub (extract v_5964 80 96) (extract v_5966 80 96)) (concat (sub (extract v_5964 96 112) (extract v_5966 96 112)) (concat (sub (extract v_5964 112 128) (extract v_5966 112 128)) (concat (sub (extract v_5964 128 144) (extract v_5966 128 144)) (concat (sub (extract v_5964 144 160) (extract v_5966 144 160)) (concat (sub (extract v_5964 160 176) (extract v_5966 160 176)) (concat (sub (extract v_5964 176 192) (extract v_5966 176 192)) (concat (sub (extract v_5964 192 208) (extract v_5966 192 208)) (concat (sub (extract v_5964 208 224) (extract v_5966 208 224)) (concat (sub (extract v_5964 224 240) (extract v_5966 224 240)) (sub (extract v_5964 240 256) (extract v_5966 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2598 : Mem) (v_2599 : reg (bv 128)) (v_2600 : reg (bv 128)) => do
      v_12029 <- getRegister v_2599;
      v_12031 <- evaluateAddress v_2598;
      v_12032 <- load v_12031 16;
      setRegister (lhs.of_reg v_2600) (concat (sub (extract v_12029 0 16) (extract v_12032 0 16)) (concat (sub (extract v_12029 16 32) (extract v_12032 16 32)) (concat (sub (extract v_12029 32 48) (extract v_12032 32 48)) (concat (sub (extract v_12029 48 64) (extract v_12032 48 64)) (concat (sub (extract v_12029 64 80) (extract v_12032 64 80)) (concat (sub (extract v_12029 80 96) (extract v_12032 80 96)) (concat (sub (extract v_12029 96 112) (extract v_12032 96 112)) (sub (extract v_12029 112 128) (extract v_12032 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2609 : Mem) (v_2610 : reg (bv 256)) (v_2611 : reg (bv 256)) => do
      v_12064 <- getRegister v_2610;
      v_12066 <- evaluateAddress v_2609;
      v_12067 <- load v_12066 32;
      setRegister (lhs.of_reg v_2611) (concat (sub (extract v_12064 0 16) (extract v_12067 0 16)) (concat (sub (extract v_12064 16 32) (extract v_12067 16 32)) (concat (sub (extract v_12064 32 48) (extract v_12067 32 48)) (concat (sub (extract v_12064 48 64) (extract v_12067 48 64)) (concat (sub (extract v_12064 64 80) (extract v_12067 64 80)) (concat (sub (extract v_12064 80 96) (extract v_12067 80 96)) (concat (sub (extract v_12064 96 112) (extract v_12067 96 112)) (concat (sub (extract v_12064 112 128) (extract v_12067 112 128)) (concat (sub (extract v_12064 128 144) (extract v_12067 128 144)) (concat (sub (extract v_12064 144 160) (extract v_12067 144 160)) (concat (sub (extract v_12064 160 176) (extract v_12067 160 176)) (concat (sub (extract v_12064 176 192) (extract v_12067 176 192)) (concat (sub (extract v_12064 192 208) (extract v_12067 192 208)) (concat (sub (extract v_12064 208 224) (extract v_12067 208 224)) (concat (sub (extract v_12064 224 240) (extract v_12067 224 240)) (sub (extract v_12064 240 256) (extract v_12067 240 256)))))))))))))))));
      pure ()
    pat_end
