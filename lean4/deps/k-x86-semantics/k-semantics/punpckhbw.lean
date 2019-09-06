def punpckhbw1 : instruction :=
  definst "punpckhbw" $ do
    pattern fun (v_3253 : reg (bv 128)) (v_3254 : reg (bv 128)) => do
      v_8686 <- getRegister v_3253;
      v_8688 <- getRegister v_3254;
      setRegister (lhs.of_reg v_3254) (concat (concat (extract v_8686 0 8) (extract v_8688 0 8)) (concat (concat (extract v_8686 8 16) (extract v_8688 8 16)) (concat (concat (extract v_8686 16 24) (extract v_8688 16 24)) (concat (concat (extract v_8686 24 32) (extract v_8688 24 32)) (concat (concat (extract v_8686 32 40) (extract v_8688 32 40)) (concat (concat (extract v_8686 40 48) (extract v_8688 40 48)) (concat (concat (extract v_8686 48 56) (extract v_8688 48 56)) (concat (extract v_8686 56 64) (extract v_8688 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_3249 : Mem) (v_3250 : reg (bv 128)) => do
      v_15089 <- evaluateAddress v_3249;
      v_15090 <- load v_15089 16;
      v_15092 <- getRegister v_3250;
      setRegister (lhs.of_reg v_3250) (concat (concat (extract v_15090 0 8) (extract v_15092 0 8)) (concat (concat (extract v_15090 8 16) (extract v_15092 8 16)) (concat (concat (extract v_15090 16 24) (extract v_15092 16 24)) (concat (concat (extract v_15090 24 32) (extract v_15092 24 32)) (concat (concat (extract v_15090 32 40) (extract v_15092 32 40)) (concat (concat (extract v_15090 40 48) (extract v_15092 40 48)) (concat (concat (extract v_15090 48 56) (extract v_15092 48 56)) (concat (extract v_15090 56 64) (extract v_15092 56 64)))))))));
      pure ()
    pat_end
