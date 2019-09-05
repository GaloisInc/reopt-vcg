def vmovsldup1 : instruction :=
  definst "vmovsldup" $ do
    pattern fun (v_3048 : reg (bv 128)) (v_3049 : reg (bv 128)) => do
      v_5071 <- getRegister v_3048;
      setRegister (lhs.of_reg v_3049) (concat (concat (extract v_5071 32 64) (extract v_5071 32 64)) (concat (extract v_5071 96 128) (extract v_5071 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3058 : reg (bv 256)) (v_3059 : reg (bv 256)) => do
      v_5082 <- getRegister v_3058;
      setRegister (lhs.of_reg v_3059) (concat (concat (concat (extract v_5082 32 64) (extract v_5082 32 64)) (concat (extract v_5082 96 128) (extract v_5082 96 128))) (concat (concat (extract v_5082 160 192) (extract v_5082 160 192)) (concat (extract v_5082 224 256) (extract v_5082 224 256))));
      pure ()
    pat_end;
    pattern fun (v_3044 : Mem) (v_3045 : reg (bv 128)) => do
      v_10243 <- evaluateAddress v_3044;
      v_10244 <- load v_10243 16;
      setRegister (lhs.of_reg v_3045) (concat (concat (extract v_10244 32 64) (extract v_10244 32 64)) (concat (extract v_10244 96 128) (extract v_10244 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3053 : Mem) (v_3054 : reg (bv 256)) => do
      v_10251 <- evaluateAddress v_3053;
      v_10252 <- load v_10251 32;
      setRegister (lhs.of_reg v_3054) (concat (concat (concat (extract v_10252 32 64) (extract v_10252 32 64)) (concat (extract v_10252 96 128) (extract v_10252 96 128))) (concat (concat (extract v_10252 160 192) (extract v_10252 160 192)) (concat (extract v_10252 224 256) (extract v_10252 224 256))));
      pure ()
    pat_end
