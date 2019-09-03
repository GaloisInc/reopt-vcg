def psubw1 : instruction :=
  definst "psubw" $ do
    pattern fun (v_3144 : reg (bv 128)) (v_3145 : reg (bv 128)) => do
      v_8987 <- getRegister v_3145;
      v_8989 <- getRegister v_3144;
      setRegister (lhs.of_reg v_3145) (concat (sub (extract v_8987 0 16) (extract v_8989 0 16)) (concat (sub (extract v_8987 16 32) (extract v_8989 16 32)) (concat (sub (extract v_8987 32 48) (extract v_8989 32 48)) (concat (sub (extract v_8987 48 64) (extract v_8989 48 64)) (concat (sub (extract v_8987 64 80) (extract v_8989 64 80)) (concat (sub (extract v_8987 80 96) (extract v_8989 80 96)) (concat (sub (extract v_8987 96 112) (extract v_8989 96 112)) (sub (extract v_8987 112 128) (extract v_8989 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3139 : Mem) (v_3140 : reg (bv 128)) => do
      v_15883 <- getRegister v_3140;
      v_15885 <- evaluateAddress v_3139;
      v_15886 <- load v_15885 16;
      setRegister (lhs.of_reg v_3140) (concat (sub (extract v_15883 0 16) (extract v_15886 0 16)) (concat (sub (extract v_15883 16 32) (extract v_15886 16 32)) (concat (sub (extract v_15883 32 48) (extract v_15886 32 48)) (concat (sub (extract v_15883 48 64) (extract v_15886 48 64)) (concat (sub (extract v_15883 64 80) (extract v_15886 64 80)) (concat (sub (extract v_15883 80 96) (extract v_15886 80 96)) (concat (sub (extract v_15883 96 112) (extract v_15886 96 112)) (sub (extract v_15883 112 128) (extract v_15886 112 128)))))))));
      pure ()
    pat_end
