def vmovsldup1 : instruction :=
  definst "vmovsldup" $ do
    pattern fun (v_2997 : reg (bv 128)) (v_2998 : reg (bv 128)) => do
      v_5386 <- getRegister v_2997;
      setRegister (lhs.of_reg v_2998) (concat (concat (extract v_5386 32 64) (extract v_5386 32 64)) (concat (extract v_5386 96 128) (extract v_5386 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3006 : reg (bv 256)) (v_3007 : reg (bv 256)) => do
      v_5397 <- getRegister v_3006;
      setRegister (lhs.of_reg v_3007) (concat (concat (concat (extract v_5397 32 64) (extract v_5397 32 64)) (concat (extract v_5397 96 128) (extract v_5397 96 128))) (concat (concat (extract v_5397 160 192) (extract v_5397 160 192)) (concat (extract v_5397 224 256) (extract v_5397 224 256))));
      pure ()
    pat_end;
    pattern fun (v_2993 : Mem) (v_2994 : reg (bv 128)) => do
      v_11182 <- evaluateAddress v_2993;
      v_11183 <- load v_11182 16;
      setRegister (lhs.of_reg v_2994) (concat (concat (extract v_11183 32 64) (extract v_11183 32 64)) (concat (extract v_11183 96 128) (extract v_11183 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3002 : Mem) (v_3003 : reg (bv 256)) => do
      v_11190 <- evaluateAddress v_3002;
      v_11191 <- load v_11190 32;
      setRegister (lhs.of_reg v_3003) (concat (concat (concat (extract v_11191 32 64) (extract v_11191 32 64)) (concat (extract v_11191 96 128) (extract v_11191 96 128))) (concat (concat (extract v_11191 160 192) (extract v_11191 160 192)) (concat (extract v_11191 224 256) (extract v_11191 224 256))));
      pure ()
    pat_end
