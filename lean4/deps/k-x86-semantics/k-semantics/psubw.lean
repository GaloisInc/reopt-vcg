def psubw1 : instruction :=
  definst "psubw" $ do
    pattern fun (v_3158 : reg (bv 128)) (v_3159 : reg (bv 128)) => do
      v_8669 <- getRegister v_3159;
      v_8671 <- getRegister v_3158;
      setRegister (lhs.of_reg v_3159) (concat (sub (extract v_8669 0 16) (extract v_8671 0 16)) (concat (sub (extract v_8669 16 32) (extract v_8671 16 32)) (concat (sub (extract v_8669 32 48) (extract v_8671 32 48)) (concat (sub (extract v_8669 48 64) (extract v_8671 48 64)) (concat (sub (extract v_8669 64 80) (extract v_8671 64 80)) (concat (sub (extract v_8669 80 96) (extract v_8671 80 96)) (concat (sub (extract v_8669 96 112) (extract v_8671 96 112)) (sub (extract v_8669 112 128) (extract v_8671 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3154 : Mem) (v_3155 : reg (bv 128)) => do
      v_15266 <- getRegister v_3155;
      v_15268 <- evaluateAddress v_3154;
      v_15269 <- load v_15268 16;
      setRegister (lhs.of_reg v_3155) (concat (sub (extract v_15266 0 16) (extract v_15269 0 16)) (concat (sub (extract v_15266 16 32) (extract v_15269 16 32)) (concat (sub (extract v_15266 32 48) (extract v_15269 32 48)) (concat (sub (extract v_15266 48 64) (extract v_15269 48 64)) (concat (sub (extract v_15266 64 80) (extract v_15269 64 80)) (concat (sub (extract v_15266 80 96) (extract v_15269 80 96)) (concat (sub (extract v_15266 96 112) (extract v_15269 96 112)) (sub (extract v_15266 112 128) (extract v_15269 112 128)))))))));
      pure ()
    pat_end
