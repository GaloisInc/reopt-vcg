def vmovshdup1 : instruction :=
  definst "vmovshdup" $ do
    pattern fun (v_3030 : reg (bv 128)) (v_3031 : reg (bv 128)) => do
      v_5043 <- getRegister v_3030;
      setRegister (lhs.of_reg v_3031) (concat (concat (extract v_5043 0 32) (extract v_5043 0 32)) (concat (extract v_5043 64 96) (extract v_5043 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3040 : reg (bv 256)) (v_3041 : reg (bv 256)) => do
      v_5054 <- getRegister v_3040;
      setRegister (lhs.of_reg v_3041) (concat (concat (concat (extract v_5054 0 32) (extract v_5054 0 32)) (concat (extract v_5054 64 96) (extract v_5054 64 96))) (concat (concat (extract v_5054 128 160) (extract v_5054 128 160)) (concat (extract v_5054 192 224) (extract v_5054 192 224))));
      pure ()
    pat_end;
    pattern fun (v_3026 : Mem) (v_3027 : reg (bv 128)) => do
      v_10221 <- evaluateAddress v_3026;
      v_10222 <- load v_10221 16;
      setRegister (lhs.of_reg v_3027) (concat (concat (extract v_10222 0 32) (extract v_10222 0 32)) (concat (extract v_10222 64 96) (extract v_10222 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3035 : Mem) (v_3036 : reg (bv 256)) => do
      v_10229 <- evaluateAddress v_3035;
      v_10230 <- load v_10229 32;
      setRegister (lhs.of_reg v_3036) (concat (concat (concat (extract v_10230 0 32) (extract v_10230 0 32)) (concat (extract v_10230 64 96) (extract v_10230 64 96))) (concat (concat (extract v_10230 128 160) (extract v_10230 128 160)) (concat (extract v_10230 192 224) (extract v_10230 192 224))));
      pure ()
    pat_end
