def vpsubw1 : instruction :=
  definst "vpsubw" $ do
    pattern fun (v_2631 : reg (bv 128)) (v_2632 : reg (bv 128)) (v_2633 : reg (bv 128)) => do
      v_5952 <- getRegister v_2632;
      v_5954 <- getRegister v_2631;
      setRegister (lhs.of_reg v_2633) (concat (sub (extract v_5952 0 16) (extract v_5954 0 16)) (concat (sub (extract v_5952 16 32) (extract v_5954 16 32)) (concat (sub (extract v_5952 32 48) (extract v_5954 32 48)) (concat (sub (extract v_5952 48 64) (extract v_5954 48 64)) (concat (sub (extract v_5952 64 80) (extract v_5954 64 80)) (concat (sub (extract v_5952 80 96) (extract v_5954 80 96)) (concat (sub (extract v_5952 96 112) (extract v_5954 96 112)) (sub (extract v_5952 112 128) (extract v_5954 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2642 : reg (bv 256)) (v_2643 : reg (bv 256)) (v_2644 : reg (bv 256)) => do
      v_5991 <- getRegister v_2643;
      v_5993 <- getRegister v_2642;
      setRegister (lhs.of_reg v_2644) (concat (sub (extract v_5991 0 16) (extract v_5993 0 16)) (concat (sub (extract v_5991 16 32) (extract v_5993 16 32)) (concat (sub (extract v_5991 32 48) (extract v_5993 32 48)) (concat (sub (extract v_5991 48 64) (extract v_5993 48 64)) (concat (sub (extract v_5991 64 80) (extract v_5993 64 80)) (concat (sub (extract v_5991 80 96) (extract v_5993 80 96)) (concat (sub (extract v_5991 96 112) (extract v_5993 96 112)) (concat (sub (extract v_5991 112 128) (extract v_5993 112 128)) (concat (sub (extract v_5991 128 144) (extract v_5993 128 144)) (concat (sub (extract v_5991 144 160) (extract v_5993 144 160)) (concat (sub (extract v_5991 160 176) (extract v_5993 160 176)) (concat (sub (extract v_5991 176 192) (extract v_5993 176 192)) (concat (sub (extract v_5991 192 208) (extract v_5993 192 208)) (concat (sub (extract v_5991 208 224) (extract v_5993 208 224)) (concat (sub (extract v_5991 224 240) (extract v_5993 224 240)) (sub (extract v_5991 240 256) (extract v_5993 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2625 : Mem) (v_2626 : reg (bv 128)) (v_2627 : reg (bv 128)) => do
      v_12056 <- getRegister v_2626;
      v_12058 <- evaluateAddress v_2625;
      v_12059 <- load v_12058 16;
      setRegister (lhs.of_reg v_2627) (concat (sub (extract v_12056 0 16) (extract v_12059 0 16)) (concat (sub (extract v_12056 16 32) (extract v_12059 16 32)) (concat (sub (extract v_12056 32 48) (extract v_12059 32 48)) (concat (sub (extract v_12056 48 64) (extract v_12059 48 64)) (concat (sub (extract v_12056 64 80) (extract v_12059 64 80)) (concat (sub (extract v_12056 80 96) (extract v_12059 80 96)) (concat (sub (extract v_12056 96 112) (extract v_12059 96 112)) (sub (extract v_12056 112 128) (extract v_12059 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2636 : Mem) (v_2637 : reg (bv 256)) (v_2638 : reg (bv 256)) => do
      v_12091 <- getRegister v_2637;
      v_12093 <- evaluateAddress v_2636;
      v_12094 <- load v_12093 32;
      setRegister (lhs.of_reg v_2638) (concat (sub (extract v_12091 0 16) (extract v_12094 0 16)) (concat (sub (extract v_12091 16 32) (extract v_12094 16 32)) (concat (sub (extract v_12091 32 48) (extract v_12094 32 48)) (concat (sub (extract v_12091 48 64) (extract v_12094 48 64)) (concat (sub (extract v_12091 64 80) (extract v_12094 64 80)) (concat (sub (extract v_12091 80 96) (extract v_12094 80 96)) (concat (sub (extract v_12091 96 112) (extract v_12094 96 112)) (concat (sub (extract v_12091 112 128) (extract v_12094 112 128)) (concat (sub (extract v_12091 128 144) (extract v_12094 128 144)) (concat (sub (extract v_12091 144 160) (extract v_12094 144 160)) (concat (sub (extract v_12091 160 176) (extract v_12094 160 176)) (concat (sub (extract v_12091 176 192) (extract v_12094 176 192)) (concat (sub (extract v_12091 192 208) (extract v_12094 192 208)) (concat (sub (extract v_12091 208 224) (extract v_12094 208 224)) (concat (sub (extract v_12091 224 240) (extract v_12094 224 240)) (sub (extract v_12091 240 256) (extract v_12094 240 256)))))))))))))))));
      pure ()
    pat_end
