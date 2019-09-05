def paddw1 : instruction :=
  definst "paddw" $ do
    pattern fun (v_3237 : reg (bv 128)) (v_3238 : reg (bv 128)) => do
      v_6228 <- getRegister v_3238;
      v_6230 <- getRegister v_3237;
      setRegister (lhs.of_reg v_3238) (concat (add (extract v_6228 0 16) (extract v_6230 0 16)) (concat (add (extract v_6228 16 32) (extract v_6230 16 32)) (concat (add (extract v_6228 32 48) (extract v_6230 32 48)) (concat (add (extract v_6228 48 64) (extract v_6230 48 64)) (concat (add (extract v_6228 64 80) (extract v_6230 64 80)) (concat (add (extract v_6228 80 96) (extract v_6230 80 96)) (concat (add (extract v_6228 96 112) (extract v_6230 96 112)) (add (extract v_6228 112 128) (extract v_6230 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3232 : Mem) (v_3233 : reg (bv 128)) => do
      v_10142 <- getRegister v_3233;
      v_10144 <- evaluateAddress v_3232;
      v_10145 <- load v_10144 16;
      setRegister (lhs.of_reg v_3233) (concat (add (extract v_10142 0 16) (extract v_10145 0 16)) (concat (add (extract v_10142 16 32) (extract v_10145 16 32)) (concat (add (extract v_10142 32 48) (extract v_10145 32 48)) (concat (add (extract v_10142 48 64) (extract v_10145 48 64)) (concat (add (extract v_10142 64 80) (extract v_10145 64 80)) (concat (add (extract v_10142 80 96) (extract v_10145 80 96)) (concat (add (extract v_10142 96 112) (extract v_10145 96 112)) (add (extract v_10142 112 128) (extract v_10145 112 128)))))))));
      pure ()
    pat_end
