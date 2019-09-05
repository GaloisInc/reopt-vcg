def vphaddd1 : instruction :=
  definst "vphaddd" $ do
    pattern fun (v_3214 : reg (bv 128)) (v_3215 : reg (bv 128)) (v_3216 : reg (bv 128)) => do
      v_8663 <- getRegister v_3214;
      v_8671 <- getRegister v_3215;
      setRegister (lhs.of_reg v_3216) (concat (concat (concat (add (extract v_8663 0 32) (extract v_8663 32 64)) (add (extract v_8663 64 96) (extract v_8663 96 128))) (add (extract v_8671 0 32) (extract v_8671 32 64))) (add (extract v_8671 64 96) (extract v_8671 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3224 : reg (bv 256)) (v_3225 : reg (bv 256)) (v_3226 : reg (bv 256)) => do
      v_8686 <- getRegister v_3224;
      v_8694 <- getRegister v_3225;
      setRegister (lhs.of_reg v_3226) (concat (concat (concat (concat (add (extract v_8686 0 32) (extract v_8686 32 64)) (add (extract v_8686 64 96) (extract v_8686 96 128))) (add (extract v_8694 0 32) (extract v_8694 32 64))) (add (extract v_8694 64 96) (extract v_8694 96 128))) (concat (concat (concat (add (extract v_8686 128 160) (extract v_8686 160 192)) (add (extract v_8686 192 224) (extract v_8686 224 256))) (add (extract v_8694 128 160) (extract v_8694 160 192))) (add (extract v_8694 192 224) (extract v_8694 224 256))));
      pure ()
    pat_end;
    pattern fun (v_3208 : Mem) (v_3209 : reg (bv 128)) (v_3210 : reg (bv 128)) => do
      v_17083 <- evaluateAddress v_3208;
      v_17084 <- load v_17083 16;
      v_17092 <- getRegister v_3209;
      setRegister (lhs.of_reg v_3210) (concat (concat (concat (add (extract v_17084 0 32) (extract v_17084 32 64)) (add (extract v_17084 64 96) (extract v_17084 96 128))) (add (extract v_17092 0 32) (extract v_17092 32 64))) (add (extract v_17092 64 96) (extract v_17092 96 128)));
      pure ()
    pat_end;
    pattern fun (v_3219 : Mem) (v_3220 : reg (bv 256)) (v_3221 : reg (bv 256)) => do
      v_17102 <- evaluateAddress v_3219;
      v_17103 <- load v_17102 32;
      v_17111 <- getRegister v_3220;
      setRegister (lhs.of_reg v_3221) (concat (concat (concat (concat (add (extract v_17103 0 32) (extract v_17103 32 64)) (add (extract v_17103 64 96) (extract v_17103 96 128))) (add (extract v_17111 0 32) (extract v_17111 32 64))) (add (extract v_17111 64 96) (extract v_17111 96 128))) (concat (concat (concat (add (extract v_17103 128 160) (extract v_17103 160 192)) (add (extract v_17103 192 224) (extract v_17103 224 256))) (add (extract v_17111 128 160) (extract v_17111 160 192))) (add (extract v_17111 192 224) (extract v_17111 224 256))));
      pure ()
    pat_end
