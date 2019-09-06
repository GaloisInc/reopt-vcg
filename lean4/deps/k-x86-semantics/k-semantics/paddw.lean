def paddw1 : instruction :=
  definst "paddw" $ do
    pattern fun (v_3262 : reg (bv 128)) (v_3263 : reg (bv 128)) => do
      v_6255 <- getRegister v_3263;
      v_6257 <- getRegister v_3262;
      setRegister (lhs.of_reg v_3263) (concat (add (extract v_6255 0 16) (extract v_6257 0 16)) (concat (add (extract v_6255 16 32) (extract v_6257 16 32)) (concat (add (extract v_6255 32 48) (extract v_6257 32 48)) (concat (add (extract v_6255 48 64) (extract v_6257 48 64)) (concat (add (extract v_6255 64 80) (extract v_6257 64 80)) (concat (add (extract v_6255 80 96) (extract v_6257 80 96)) (concat (add (extract v_6255 96 112) (extract v_6257 96 112)) (add (extract v_6255 112 128) (extract v_6257 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3258 : Mem) (v_3259 : reg (bv 128)) => do
      v_10169 <- getRegister v_3259;
      v_10171 <- evaluateAddress v_3258;
      v_10172 <- load v_10171 16;
      setRegister (lhs.of_reg v_3259) (concat (add (extract v_10169 0 16) (extract v_10172 0 16)) (concat (add (extract v_10169 16 32) (extract v_10172 16 32)) (concat (add (extract v_10169 32 48) (extract v_10172 32 48)) (concat (add (extract v_10169 48 64) (extract v_10172 48 64)) (concat (add (extract v_10169 64 80) (extract v_10172 64 80)) (concat (add (extract v_10169 80 96) (extract v_10172 80 96)) (concat (add (extract v_10169 96 112) (extract v_10172 96 112)) (add (extract v_10169 112 128) (extract v_10172 112 128)))))))));
      pure ()
    pat_end
