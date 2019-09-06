def vmovsldup1 : instruction :=
  definst "vmovsldup" $ do
    pattern fun (v_3073 : reg (bv 128)) (v_3074 : reg (bv 128)) => do
      v_5098 <- getRegister v_3073;
      setRegister (lhs.of_reg v_3074) (concat (concat (extract v_5098 32 64) (extract v_5098 32 64)) (concat (extract v_5098 96 128) (extract v_5098 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3082 : reg (bv 256)) (v_3083 : reg (bv 256)) => do
      v_5109 <- getRegister v_3082;
      setRegister (lhs.of_reg v_3083) (concat (concat (concat (extract v_5109 32 64) (extract v_5109 32 64)) (concat (extract v_5109 96 128) (extract v_5109 96 128))) (concat (concat (extract v_5109 160 192) (extract v_5109 160 192)) (concat (extract v_5109 224 256) (extract v_5109 224 256))));
      pure ()
    pat_end;
    pattern fun (v_3069 : Mem) (v_3070 : reg (bv 128)) => do
      v_10270 <- evaluateAddress v_3069;
      v_10271 <- load v_10270 16;
      setRegister (lhs.of_reg v_3070) (concat (concat (extract v_10271 32 64) (extract v_10271 32 64)) (concat (extract v_10271 96 128) (extract v_10271 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3078 : Mem) (v_3079 : reg (bv 256)) => do
      v_10278 <- evaluateAddress v_3078;
      v_10279 <- load v_10278 32;
      setRegister (lhs.of_reg v_3079) (concat (concat (concat (extract v_10279 32 64) (extract v_10279 32 64)) (concat (extract v_10279 96 128) (extract v_10279 96 128))) (concat (concat (extract v_10279 160 192) (extract v_10279 160 192)) (concat (extract v_10279 224 256) (extract v_10279 224 256))));
      pure ()
    pat_end
