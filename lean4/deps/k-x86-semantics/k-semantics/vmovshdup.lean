def vmovshdup1 : instruction :=
  definst "vmovshdup" $ do
    pattern fun (v_2979 : reg (bv 128)) (v_2980 : reg (bv 128)) => do
      v_5358 <- getRegister v_2979;
      setRegister (lhs.of_reg v_2980) (concat (concat (extract v_5358 0 32) (extract v_5358 0 32)) (concat (extract v_5358 64 96) (extract v_5358 64 96)));
      pure ()
    pat_end;
    pattern fun (v_2988 : reg (bv 256)) (v_2989 : reg (bv 256)) => do
      v_5369 <- getRegister v_2988;
      setRegister (lhs.of_reg v_2989) (concat (concat (concat (extract v_5369 0 32) (extract v_5369 0 32)) (concat (extract v_5369 64 96) (extract v_5369 64 96))) (concat (concat (extract v_5369 128 160) (extract v_5369 128 160)) (concat (extract v_5369 192 224) (extract v_5369 192 224))));
      pure ()
    pat_end;
    pattern fun (v_2975 : Mem) (v_2976 : reg (bv 128)) => do
      v_11160 <- evaluateAddress v_2975;
      v_11161 <- load v_11160 16;
      setRegister (lhs.of_reg v_2976) (concat (concat (extract v_11161 0 32) (extract v_11161 0 32)) (concat (extract v_11161 64 96) (extract v_11161 64 96)));
      pure ()
    pat_end;
    pattern fun (v_2984 : Mem) (v_2985 : reg (bv 256)) => do
      v_11168 <- evaluateAddress v_2984;
      v_11169 <- load v_11168 32;
      setRegister (lhs.of_reg v_2985) (concat (concat (concat (extract v_11169 0 32) (extract v_11169 0 32)) (concat (extract v_11169 64 96) (extract v_11169 64 96))) (concat (concat (extract v_11169 128 160) (extract v_11169 128 160)) (concat (extract v_11169 192 224) (extract v_11169 192 224))));
      pure ()
    pat_end
