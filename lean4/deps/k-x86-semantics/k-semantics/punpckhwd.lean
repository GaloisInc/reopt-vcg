def punpckhwd1 : instruction :=
  definst "punpckhwd" $ do
    pattern fun (v_3203 : reg (bv 128)) (v_3204 : reg (bv 128)) => do
      v_8787 <- getRegister v_3203;
      v_8789 <- getRegister v_3204;
      setRegister (lhs.of_reg v_3204) (concat (concat (extract v_8787 0 16) (extract v_8789 0 16)) (concat (concat (extract v_8787 16 32) (extract v_8789 16 32)) (concat (concat (extract v_8787 32 48) (extract v_8789 32 48)) (concat (extract v_8787 48 64) (extract v_8789 48 64)))));
      pure ()
    pat_end;
    pattern fun (v_3199 : Mem) (v_3200 : reg (bv 128)) => do
      v_15369 <- evaluateAddress v_3199;
      v_15370 <- load v_15369 16;
      v_15372 <- getRegister v_3200;
      setRegister (lhs.of_reg v_3200) (concat (concat (extract v_15370 0 16) (extract v_15372 0 16)) (concat (concat (extract v_15370 16 32) (extract v_15372 16 32)) (concat (concat (extract v_15370 32 48) (extract v_15372 32 48)) (concat (extract v_15370 48 64) (extract v_15372 48 64)))));
      pure ()
    pat_end
