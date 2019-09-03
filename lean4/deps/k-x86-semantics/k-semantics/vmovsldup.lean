def vmovsldup1 : instruction :=
  definst "vmovsldup" $ do
    pattern fun (v_2985 : reg (bv 128)) (v_2986 : reg (bv 128)) => do
      v_5013 <- getRegister v_2985;
      setRegister (lhs.of_reg v_2986) (concat (concat (extract v_5013 32 64) (extract v_5013 32 64)) (concat (extract v_5013 96 128) (extract v_5013 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2994 : reg (bv 256)) (v_2995 : reg (bv 256)) => do
      v_5024 <- getRegister v_2994;
      setRegister (lhs.of_reg v_2995) (concat (concat (concat (extract v_5024 32 64) (extract v_5024 32 64)) (concat (extract v_5024 96 128) (extract v_5024 96 128))) (concat (concat (extract v_5024 160 192) (extract v_5024 160 192)) (concat (extract v_5024 224 256) (extract v_5024 224 256))));
      pure ()
    pat_end;
    pattern fun (v_2980 : Mem) (v_2981 : reg (bv 128)) => do
      v_10377 <- evaluateAddress v_2980;
      v_10378 <- load v_10377 16;
      setRegister (lhs.of_reg v_2981) (concat (concat (extract v_10378 32 64) (extract v_10378 32 64)) (concat (extract v_10378 96 128) (extract v_10378 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2989 : Mem) (v_2990 : reg (bv 256)) => do
      v_10385 <- evaluateAddress v_2989;
      v_10386 <- load v_10385 32;
      setRegister (lhs.of_reg v_2990) (concat (concat (concat (extract v_10386 32 64) (extract v_10386 32 64)) (concat (extract v_10386 96 128) (extract v_10386 96 128))) (concat (concat (extract v_10386 160 192) (extract v_10386 160 192)) (concat (extract v_10386 224 256) (extract v_10386 224 256))));
      pure ()
    pat_end
